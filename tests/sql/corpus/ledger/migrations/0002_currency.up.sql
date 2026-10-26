SET statement_timeout = '1min';

ALTER TABLE accounts ADD COLUMN currency TEXT NOT NULL DEFAULT '';
CREATE UNIQUE INDEX accounts_name_currency ON accounts (name, currency);

ALTER TABLE balances ALTER COLUMN floor_amount SET DEFAULT -100;

-- Data, not schema: tolean skips it.
UPDATE accounts SET name = CASE WHEN name = '' THEN 'unnamed' ELSE name END;
