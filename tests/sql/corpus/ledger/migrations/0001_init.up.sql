-- A double-entry ledger: every transfer debits one account and credits
-- another by the same amount, so the sum of all balances never changes.
CREATE TYPE account_state AS ENUM ('open', 'frozen');

CREATE DOMAIN account_key AS UUID;

CREATE TABLE accounts (
  id account_key PRIMARY KEY,
  name TEXT NOT NULL,
  state account_state NOT NULL DEFAULT 'open',
  closed_at TIMESTAMPTZ,
  extra JSONB,
  opened_at TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE TABLE balances (
  account account_key PRIMARY KEY REFERENCES accounts(id) ON DELETE CASCADE,
  amount BIGINT NOT NULL DEFAULT 0,
  floor_amount BIGINT NOT NULL DEFAULT 0,
  state account_state NOT NULL,
  posted_at TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE INDEX balances_by_state ON balances (state);

-- The queries never read this table, so tolean skips what concerns it.
CREATE TABLE journal (
  id BIGINT PRIMARY KEY,
  body JSONB NOT NULL,
  CHECK (body ? 'lines')
);
