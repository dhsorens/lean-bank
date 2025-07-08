-- This module serves as the root of the `Bank` library.
-- Import modules here that should be built as part of the library.
import Bank.Vault

-- bank data struct
structure Bank where
  vault : Vault
  account_nonce : Nat

-- initialize
def init_bank : Bank := {
  vault := init_vault,
  account_nonce := 0
}

-- open an account
def open_account (b : Bank) : Except String (Bank × Nat) :=
  let new_id := b.account_nonce + 1
  if (is_account new_id b.vault) then
  Except.error "Account already open." else
  Except.ok
    ({ b with
      vault := deposit new_id 0 b.vault ,
      account_nonce := new_id },
    new_id)

-- close an account
def close_account (id : Nat) (b : Bank) : Except String Bank := do
  if !(is_account id b.vault) then
  Except.error "No account found." else
  let v ← acct_destroy id b.vault
  Except.ok { b with vault := v }

-- transaction types
inductive Txn
| Deposit (id amt : Nat)
| Withdraw (id amt : Nat)
| Transfer (id_from id_to amt : Nat)

-- transact
def transact (t : Txn) (b : Bank) : Except String Bank := do
  -- transaction executes
  match t with
  | .Deposit id amt =>
    if !(is_account id b.vault) then
    Except.error "Must be an account to transact" else
    Except.ok { b with vault := deposit id amt b.vault }
  | .Withdraw id amt =>
    if !(is_account id b.vault) then
    Except.error "Must be an account to transact" else
    let v ← withdraw id amt b.vault
    Except.ok { b with vault := v }
  | .Transfer id_from id_to amt =>
    if !(is_account id_from b.vault) || !(is_account id_to b.vault) then
    Except.error "Must be an account to transact" else
    let v ← withdraw id_from amt b.vault
    Except.ok { b with vault := deposit id_to amt v }

--
def bank_bal (id : Nat) (b : Bank) : Except String Nat :=
  query_balance_ex id b.vault
