import Lean.Data.RBMap
open Lean.RBNode

-- aux
def toExcept {α} (msg : String) (o : Option α) : Except String α :=
  match o with
  | some a => Except.ok a
  | none   => Except.error msg

def Map := Lean.RBMap

-- the vault keeps track of accounts
structure Vault where
  accounts : Map Nat Nat compare

-- initialization
def init_vault : Vault := {
  accounts := Lean.RBMap.empty
}

-- some view functions
def query_balance (id : Nat) (v : Vault) : Nat :=
  v.accounts.findD id 0

def query_balance_ex (id : Nat) (v : Vault) : Except String Nat :=
  toExcept "No account found." (v.accounts.find? id)

def is_account (id : Nat) (v : Vault) : Bool :=
  v.accounts.contains id

-- three entrypoints: deposit, withdraw, transfer
def deposit (id qty : Nat) (v : Vault) : Vault :=
  { v with
    accounts := v.accounts.insert id (v.accounts.findD id 0 + qty)
  }

def withdraw (id qty : Nat) (v : Vault) : Except String Vault := do
  let bal ← toExcept "Err in lookup" (v.accounts.find? id)
  if qty ≤ bal then
    Except.ok { v with accounts :=
      v.accounts.insert id (v.accounts.findD id 0 - qty) }
  else
    Except.error "Insufficient funds for withdrawal."

-- account creation and deletion
def acct_create (id : Nat) (v : Vault) : Except String Vault :=
  match v.accounts.find? id with
  | none => Except.ok { v with accounts := v.accounts.insert id 0 }
  | some _ => Except.error "Account already exists with that id."

def acct_destroy (id : Nat) (v : Vault) : Except String Vault := do
  let b ← toExcept "Err in lookup" (v.accounts.find? id)
  if b > 0 then
    Except.error "To close an account, the account balance must be zero."
  else
  Except.ok { v with accounts := v.accounts.erase id }
