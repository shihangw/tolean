import access.Rbac

namespace Spec
open access.Rbac

/-- Tenant isolation: a binding or a deny rule in another tenant never changes
a decision. -/
def tenant_isolation : Prop :=
  ∀ (p : Policy) (req : Request) (b : Binding) (d : Deny),
    b.tenant ≠ req.tenant → d.tenant ≠ req.tenant →
    permits { p with bindings := p.bindings ++ [b], denies := p.denies ++ [d] } req = permits p req

/-- A deny rule that applies overrides every binding. -/
def deny_wins : Prop :=
  ∀ (p : Policy) (req : Request) (d : Deny),
    d ∈ p.denies → denyApplies p d req = true → permits p req = false

/-- Access needs a binding in the request's tenant, whose member holds the
principal and whose role grants the permission. -/
def needs_binding : Prop :=
  ∀ (p : Policy) (req : Request), permits p req = true →
    ∃ b ∈ p.bindings, b.tenant = req.tenant ∧ isMember p.groups b.member req.principal = true ∧
      roleGrants p.grants b.role req.permission = true

/-- A binding to a group grants its permissions to each principal in the
group, unless a deny rule applies. -/
def group_grants : Prop :=
  ∀ (p : Policy) (req : Request) (b : Binding),
    b ∈ p.bindings → b.tenant = req.tenant → inGroup p.groups b.member req.principal = true →
    roleGrants p.grants b.role req.permission = true → denied p req = false →
    permits p req = true

/-- Adding a deny rule never grants access that was refused. -/
def deny_never_grants : Prop :=
  ∀ (p : Policy) (req : Request) (d : Deny),
    permits { p with denies := p.denies ++ [d] } req = true → permits p req = true

end Spec
