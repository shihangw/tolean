/** A role binding: in one tenant, a member holds a role. The member is a
principal or a group. */
export interface Binding {
  readonly tenant: string;
  readonly role: string;
  readonly member: string;
}

/** A role grants a permission. */
export interface Grant {
  readonly role: string;
  readonly permission: string;
}

/** A principal belongs to a group. */
export interface Membership {
  readonly group: string;
  readonly principal: string;
}

/** A deny rule: in one tenant, a member may not use a permission. */
export interface Deny {
  readonly tenant: string;
  readonly permission: string;
  readonly member: string;
}

export interface Policy {
  readonly bindings: ReadonlyArray<Binding>;
  readonly grants: ReadonlyArray<Grant>;
  readonly groups: ReadonlyArray<Membership>;
  readonly denies: ReadonlyArray<Deny>;
}

/** A principal asks to use a permission in a tenant. */
export interface Request {
  readonly tenant: string;
  readonly principal: string;
  readonly permission: string;
}

export function inGroup(groups: ReadonlyArray<Membership>, group: string, principal: string): boolean {
  let found = false;
  for (const m of groups) {
    if (m.group === group && m.principal === principal) {
      found = true;
    }
  }
  return found;
}

/** The member is the principal itself, or a group that holds the principal. */
export function isMember(groups: ReadonlyArray<Membership>, member: string, principal: string): boolean {
  return member === principal || inGroup(groups, member, principal);
}

export function roleGrants(grants: ReadonlyArray<Grant>, role: string, permission: string): boolean {
  let found = false;
  for (const g of grants) {
    if (g.role === role && g.permission === permission) {
      found = true;
    }
  }
  return found;
}

export function bindingAllows(p: Policy, b: Binding, req: Request): boolean {
  return b.tenant === req.tenant && isMember(p.groups, b.member, req.principal) &&
    roleGrants(p.grants, b.role, req.permission);
}

export function denyApplies(p: Policy, d: Deny, req: Request): boolean {
  return d.tenant === req.tenant && d.permission === req.permission &&
    isMember(p.groups, d.member, req.principal);
}

export function allowed(p: Policy, req: Request): boolean {
  let found = false;
  for (const b of p.bindings) {
    if (bindingAllows(p, b, req)) {
      found = true;
    }
  }
  return found;
}

export function denied(p: Policy, req: Request): boolean {
  let found = false;
  for (const d of p.denies) {
    if (denyApplies(p, d, req)) {
      found = true;
    }
  }
  return found;
}

/** Allow when a binding in the tenant allows, and no deny rule applies. */
export function permits(p: Policy, req: Request): boolean {
  return allowed(p, req) && !denied(p, req);
}
