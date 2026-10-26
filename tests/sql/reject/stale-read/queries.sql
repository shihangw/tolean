-- name: Debit :one
-- One side of a double entry: take n from an account, down to its floor.
UPDATE balances
SET amount = amount - sqlc.arg(n)::bigint, posted_at = now()
WHERE account = sqlc.arg(account)::uuid
  AND sqlc.arg(n)::bigint > 0
  AND amount - sqlc.arg(n)::bigint >= floor_amount
  AND NOT EXISTS (
    SELECT 1 FROM accounts a WHERE a.id = sqlc.arg(account)::uuid AND a.closed_at IS NOT NULL
  )
RETURNING amount;

-- name: Credit :one
-- The other side: add n to an open account.
WITH target AS (
  SELECT b.account
  FROM balances b
  JOIN accounts a ON a.id = b.account
  WHERE b.account = sqlc.arg(account)::uuid AND a.state = 'open' AND sqlc.arg(n)::bigint > 0
), added AS (
  UPDATE balances b
  SET amount = b.amount + sqlc.arg(n)::bigint, posted_at = now()
  FROM target
  WHERE b.account = target.account
  RETURNING b.amount
)
SELECT (SELECT amount FROM added) AS balance;

-- name: Freeze :execrows
UPDATE balances SET state = 'frozen'
WHERE account = sqlc.arg(account)::uuid AND amount >= floor_amount;

-- name: GetAccount :one
SELECT a.name, b.amount - b.floor_amount AS available, a.state::text AS state,
  COALESCE(a.closed_at, now()) AS until, a.closed_at IS NULL AS open
FROM accounts a
JOIN balances b ON b.account = a.id
WHERE a.id = sqlc.arg(account)::uuid;
