# Plan: asynchronous TypeScript and race conditions

**Status:** planned, not built · **Date:** 2026-11-04

Most TypeScript that talks to the outside world is `async`, and Tolean
refuses all of it today. This plan adds `async` and `await` in two levels.
The first level covers code that awaits every promise at once, which is most
code, and translates it as ordinary monadic Lean. The second level covers code
that runs several calls at the same time. It gives each function a form in
which a person can prove that a race condition cannot happen, or show the
schedule that causes one.

The [effects plan](effects.md) fixes the boundary where translated code calls
a library. This plan builds on it but stays separate, because it needs things
that the effects plan does not: a job queue in the interpreter, a meaning for
code that interleaves, and a new kind of claim. The
[shared core plan](shared-core.md) also keeps the concurrency model with each
language, because the event loop, Go's scheduler and READ COMMITTED differ too
much to share.

## 1. What JavaScript does at an `await`

JavaScript runs one job at a time, and a job runs until it finishes or reaches
an `await`. So the code between two `await`s runs as one atomic step. Three
details of ECMA-262 decide how Tolean can model this.

1. **Every `await` yields.** This holds even when the value is not a promise,
   or is a promise that has already resolved. The rest of the function runs
   as a later job, and other jobs can run first. So the code before an
   `await` and the code after it are never one atomic step.
2. **An `async` function runs its body at once, up to its first `await`.**
   Only then does it return a promise to its caller.
3. **A `throw` in an `async` function rejects its promise.** The caller does
   not see a synchronous exception. It sees the rejection when it awaits the
   promise.

## 2. Level one: code that awaits every promise at once

Here the subset allows `await f(x)` only where `f(x)` is a call, and every call
to an `async` function must be awaited at once. It refuses `.then`, `.catch`,
`.finally`, `Promise.all`, `Promise.race`, and a call whose promise the code
keeps or drops. With these rules, only one chain of calls is ever pending, so
nothing can interleave with it.

The translation is the one that the effects plan uses for any effectful
function. An `async` function that returns `Promise<T>` becomes a Lean
function that returns `m T`, with class constraints on `m`. Each `await e`
becomes `let v ← e`, followed by a yield. A rejection, or a `throw` in the
body, becomes an exception in `ExceptT`. Detail 3 does not matter here,
because the caller awaits at once and sees the exception either way. A call
to a library that is awaited is a declared external call, so a theorem holds
for every answer that the outside world gives, as Go's interface calls do
today.

```ts
async function getUser(id: string): Promise<User> {
  const row = await db.find(id);
  if (!row) throw new NotFound(id);
  return toUser(row);
}
```

```lean
def getUser [Monad m] [MonadExcept Err m] [Reads Db m] [Await m]
    (id : JSString) : m User := do
  let row ← Db.find id
  Await.yield
  match row with
  | none   => throw (.notFound id)
  | some r => pure (toUser r)
```

`Await.yield` marks the point where other jobs may run. Its law is a rely
condition, which states what the rest of the program may do at that point. A
yield leaves the state that the function owns unchanged, and it may change any
shared resource in any way. The subset lets a function change only the locals
that it owns, so today a yield never changes a value. One rewrite removes it
from a proof, as one rewrite removes telemetry in the effects plan. Once the
subset has shared objects or a module-level `let`, the law stops a proof from
assuming that a shared value stays the same across an `await`.

The theorem that makes this level sound belongs to the interpreter. The
TypeScript interpreter gains a job queue, as ECMA-262 describes it. Then a
theorem states that, for every program at this level, running it with the job
queue gives the same result as running it directly in the monad. The proof
should be short, because the queue never holds more than one job of the
program. With this theorem, `program_sound` and the certificates carry over to
`async` code without a new kind of statement. The generated code uses
`StateT` and `ExceptT`, so `Std.Do` reasons about it too.

## 3. Level two: races

A race in JavaScript is always an atomicity violation across an `await`. The
code reads a value, yields, and then acts on that value, which may now be
stale. Two lines never run at the same moment, so this is the only kind of
race that JavaScript has.

```ts
async function withdraw(acct: string, amt: number) {
  const bal = await db.getBalance(acct);
  if (bal >= amt) await db.subtract(acct, amt);
}
```

Two calls at once can both read 100 and both pass the check. Then both take
60, and the account ends at -20. If the code wrote `setBalance(acct, bal -
amt)` instead, both calls would write 40, and the account would pay out 120
while it records only 60. That is a lost update, the other face of the same
race. The same shape appears in other common code:

- **Lazy setup.** `if (!client) client = await connect()` can open two
  connections.
- **Stale responses.** In search as you type, an older response can arrive
  last and overwrite a newer one.
- **Webhook handlers.** A provider may deliver one event twice at the same
  time, or deliver events out of order. A handler that checks whether it has
  seen an event and then records it can handle the event twice.
- **Caches.** `if (!cache.has(k)) cache.set(k, await load(k))` can overwrite
  a fresh value with an old one.

### The form of a function

At this level, each `await` splits a function into segments, and each segment
is one atomic step on a shared world. The world holds every shared resource,
such as a module-level variable or a declared resource from the effects plan.
A proof plugs in a model of each declared resource, as it plugs in a model of
a Go store today. The translator writes each function as a task, of the Lean
type `Steps`. A task is either done, or it is one atomic step on the world
followed by the rest of the task. The name avoids Lean's own `Task`, which is
a thread.

```lean
inductive Steps (W α : Type) : Type 1 where
  | done : α → Steps W α
  | step : {β : Type} → (W → W × β) → (β → Steps W α) → Steps W α

def withdraw (a : Acct) (amt : Int) : Steps World Unit :=
  .step (fun w => (w, w.balance a)) fun bal =>
  .step (fun w => if bal ≥ amt
                  then ({ w with balance := update w.balance a (w.balance a - amt) }, ())
                  else (w, ())) fun _ =>
  .done ()
```

The second step checks `bal`, which the first step read, but it subtracts
from the balance that the world holds now. That gap is the race.

A schedule picks which pending task takes its next step. `runAll` runs a list
of tasks under a schedule. A race claim states that an invariant holds under
every schedule, for any number of calls:

```lean
def Safe := ∀ (calls : List (Steps World Unit)) (sched : Schedule) (w : World),
  NonNeg w → NonNeg (runAll calls sched w)
```

Treating the scheduler as arbitrary allows more schedules than a real engine
does, because it ignores the order of the job queues. So a proof of `Safe`
holds for every real engine. A claim that depends on the order of jobs stays
out of scope.

### How a proof goes

A proof does not list the schedules. Tolean proves one rule once, in the style
of Owicki and Gries: if every step of every task keeps the invariant, the
invariant holds under every schedule. A step may assume only the invariant,
and what its own task knows, because any other step may have run since the
task's last step. So each proof obligation is about one segment of one
function.

When the code has a race, the obligation for some segment cannot be proved,
and that segment is where the race is. For `withdraw`, the second segment
needs `w.balance a ≥ amt` so that the balance stays at zero or above. But it
knows only `bal ≥ amt`, and another call may have taken money since the first
segment read `bal`. A person can then prove
`¬ Safe` with two calls and the schedule that runs both reads before both
writes. The kernel checks that schedule with `decide`, so the race report is a
theorem, not a warning.

The fix makes the check and the write one step. One SQL statement, such as
`UPDATE accounts SET bal = bal - $1 WHERE id = $2 AND bal >= $1`, is one call,
so `withdraw` becomes one segment, and the proof of `Safe` is short.

### Claims beyond invariants

The same form supports three more kinds of claim. Each is worth having for
code that handles money or shared state.

| Claim | Example |
|---|---|
| A protocol on the trace of external calls | Every transaction ends in a commit or a rollback, and a lock is released on every path, including a `throw`. |
| Idempotence | Running a webhook handler twice on one event leaves the world as running it once does. |
| Linearizability | A cache that shares requests already in flight behaves as plain memoization, as if the calls ran one after another. |

## 4. Races that cross into the database

Whether `withdraw` is safe depends on the database as much as on the
TypeScript. A `SELECT … FOR UPDATE` removes the race, and a plain `SELECT`
under READ COMMITTED does not. Tolean already proves a model of READ
COMMITTED in `tolean/Sql/Spec/ReadCommitted.lean`. Its first theorem has the
same shape as the rule in section 3: if every update keeps a property of a
row, every committed row has it.

So a database call in the world of a task can step the READ COMMITTED model,
instead of a model that a person writes. Then one claim covers both layers,
such as "this handler cannot charge a customer twice under READ COMMITTED".
The model already refuses an `UPDATE` that writes a value it read from its own
table without a lock, so the two layers refuse the same mistake.

## 5. Finding races and proving their absence

Lean proves that a race cannot happen. It is a slow way to find one. A
scheduler that reorders when promises resolve, such as `fc.scheduler()` in
fast-check, finds a race in a test run in seconds. The chain already has a
stage for this: the effects plan moves a boundary from declared, to tested,
to proved. A race claim can move the same way. A scheduler test marks it
tested, and a Lean proof of `Safe` marks it proved.

## 6. What stays refused

- Behavior that depends on the order of jobs, such as which of two resolved
  promises runs its callback first.
- `setTimeout`, `setInterval` and anything else that depends on time.
- A promise that the code neither awaits nor passes to `Promise.all`, until
  the plan has a claim about what a dropped rejection does.
- Async iteration, `for await` and async generators.
- Claims that a call finishes. Value claims stay partial, as the effects plan
  states, because a promise that never settles never resumes its caller.

## 7. Steps

Each step ends with all checks green, and with no change to the output of code
that has no `async`.

1. Write `withdraw.ts` twice, with the race and with the one-statement fix.
   Write the task form of each by hand, prove `¬ Safe` for the first and
   `Safe` for the second, and record how long each proof is. If the proofs
   are not short, rethink section 3 before the translator changes.
2. Give the TypeScript interpreter a job queue, with `async` and `await` as
   ECMA-262 defines them. Add corpus files that compare the interpreter with
   Node.
3. Translate level one. Add the `Await` class and its law, the rules that
   refuse a promise not awaited at once, and the theorem that the job queue
   and the monad agree. Extend `program_sound` and the certificates. This step
   needs step 3 of the shared core plan, which adds state and exceptions.
4. Add `Steps`, schedules, `runAll` and the rule from section 3 in
   `tolean/TypeScript/Async/`. Translate functions that touch a shared
   resource into the task form, and prove that each task computes what the
   interpreter computes for every schedule that the job queue allows.
5. Allow `Promise.all`, as all interleavings of its tasks. Model that it
   rejects as soon as one task rejects, while the other tasks keep running and
   can still change the world.
6. Let a database call step the READ COMMITTED model, and certify one handler
   whose claim crosses both layers.
7. Add a chain check that runs each race claim's function under a randomized
   scheduler in Node and marks the claim tested.

## Open questions

- Should the translator always write the task form, or only for functions
  that touch a shared resource? The task form is harder to read, so the plan
  assumes the second.
- Where does a person write a race claim: in `tolean.json` with the other
  claims, or only as a Lean theorem?
- How should a claim name the set of calls it allows to run together, such as
  "any number of `withdraw` calls and at most one `close`"?

## Prior work

- Madsen, Lhoták and Tip, *A Model for Reasoning About JavaScript Promises*,
  OOPSLA 2017, gives a core calculus for promises and their job queue.
- Xia and others, *Interaction Trees*, POPL 2020, represent effectful programs
  as trees of requests and answers, the shape of `Steps` above.
- Owicki and Gries, and Jones's rely-guarantee method, prove properties of
  interleaved programs one step at a time.
