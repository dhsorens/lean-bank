import Bank.Vault
import Bank.VaultLemmas

-- Some properties of correctness for the vault

-- create and destroy don't affect total balances
-- balance can never go negative (from withdraw)
-- only accounts at 0 can be destroyed

-- functional correctness
-- DEPOSITS
theorem vault_deposit_correct : ∀ id qty v_prev v_next,
  -- a successful deposit
  deposit id qty v_prev = v_next →
  -- compare balances in line with the deposit
  let bal_prev := query_balance id v_prev
  let bal_next := query_balance id v_next
  bal_next = bal_prev + qty := by
  simp
  intro id qty v_prev
  unfold deposit query_balance
  simp
  rw [rbmap_insert_find]

#check ite

-- WITHDRAWALS
theorem vault_withdraw_correct : ∀ id qty v_prev v_next,
  -- a successful withdrawal
  withdraw id qty v_prev = Except.ok v_next →
  -- compare balances in line with the withdrawal
  let bal_prev := query_balance id v_prev
  let bal_next := query_balance id v_next
  bal_next = bal_prev - qty := by
  simp
  intro id qty v_prev v_next
  unfold withdraw query_balance toExcept
  cases (Lean.RBMap.find? v_prev.accounts id) with
  | none =>
    intro h_contradiction
    contradiction
  | some b =>
    simp
    unfold Monad.toBind
    unfold Except.instMonad
    simp
    unfold Except.bind
    simp
    split
    . intro h_ok
      injection h_ok with h_vault
      rw [← h_vault]
      simp
      apply rbmap_insert_findD
    . intro h_contradiction
      contradiction

-- failure condition
theorem vault_withdraw_correct_err : ∀ id qty v,
  let bal_prev := query_balance id v
  bal_prev < qty →
  -- a successful withdrawal
  ∃ e, withdraw id qty v = Except.error e := by
  intro id qty v
  simp
  unfold withdraw query_balance Lean.RBMap.findD
  cases (Lean.RBMap.find? v.accounts id) with
  | none =>
    simp
    intro h_lt
    exists "Err in lookup"
  | some b =>
    intro h_lt
    exists "Insufficient funds for withdrawal."
    unfold toExcept
    unfold Except.instMonad
    unfold Except.bind
    simp
    assumption

-- ACCOUNT CREATION
theorem vault_create_correct : ∀ id v_prev v_next,
  -- a successful account creation
  acct_create id v_prev = Except.ok v_next →
  -- the new account has zero balance
  query_balance id v_next = 0 ∧
  -- all other balances are unchanged
  ∀ id', id' ≠ id →
  query_balance id' v_next = query_balance id' v_prev := by
  intro id v_prev v_next
  unfold acct_create
  cases (Lean.RBMap.find? v_prev.accounts id) with
  | some _ => simp -- failure case
  | none => -- success case
    simp
    intro h_v
    rw [← h_v]
    unfold query_balance
    rw [rbmap_insert_findD]
    constructor
    . trivial
    . intro id'
      simp
      apply rbmap_insert_find_neq

-- Creating an account that already exists fails
  theorem vault_create_fail : ∀ id v_prev bal,
    query_balance_ex id v_prev = Except.ok bal →
    ∃ e, acct_create id v_prev = Except.error e := by
    intro id v_prev bal
    unfold query_balance_ex
    unfold acct_create
    cases (Lean.RBMap.find? v_prev.accounts id) with
    | none =>
      intro h_contradiction
      contradiction
    | some b => simp

-- ACCOUNT DESTRUCTION
theorem vault_destroy_correct : ∀ id v_prev v_next,
  -- a successful account destruction
  acct_destroy id v_prev = Except.ok v_next →
  -- the account is removed (balance is zero and not present)
  query_balance id v_prev = 0 ∧
  -- all other balances are unchanged
  ∀ id', id' ≠ id →
    query_balance id' v_next = query_balance id' v_prev := by
  intro id v_prev v_next
  unfold acct_destroy toExcept query_balance Lean.RBMap.findD
  cases (Lean.RBMap.find? v_prev.accounts id) with
  | none =>
    simp
    intro h_contradiction
    contradiction
  | some b =>
    simp
    unfold Monad.toBind
    unfold Except.instMonad
    unfold Except.bind
    simp
    split
    . intro h_contradiction
      contradiction
    . intro h_vault
      injection h_vault with h_vault
      rw [← h_vault]
      constructor
      . clear h_vault
        apply Nat.eq_zero_of_not_pos
        assumption
      . intro id' h_neq
        apply rbmap_erase_find_neq
        assumption

-- Destroying a non-existent account fails
theorem vault_destroy_fail_no_account : ∀ id v_prev e,
  query_balance_ex id v_prev = Except.error e →
  ∃ e', acct_destroy id v_prev = Except.error e' := by
  intro id v_prev e
  unfold query_balance_ex toExcept acct_destroy
  cases Lean.RBMap.find? v_prev.accounts id with
  | none =>
    simp
    intro h_e
    unfold toExcept
    simp
    unfold Except.instMonad
    unfold Monad.toBind
    unfold Except.bind
    simp
  | some b =>
    simp

-- Destroying an account with nonzero balance fails
theorem vault_destroy_fail_nonzero : ∀ id bal v_prev,
  query_balance_ex id v_prev = Except.ok bal →
  bal > 0 →
  ∃ e, acct_destroy id v_prev = Except.error e := by
  intro id bal v_prev
  unfold acct_destroy query_balance_ex toExcept at *
  simp at *
  cases Lean.RBMap.find? v_prev.accounts id with
  | none =>
    unfold Except.instMonad
    unfold Monad.toBind
    unfold Except.bind
    simp
  | some b =>
    simp
    intro h_b h_bal
    exists "To close an account, the account balance must be zero."
    unfold Except.instMonad
    unfold Monad.toBind
    unfold Except.bind
    simp
    apply Nat.ne_zero_iff_zero_lt.mpr
    rw [h_b]
    assumption


-- TODO transfer does not change total balance



-- INVARIANTS
-- To write invariants, we need a formalization of the vault's trace.

-- step
inductive vault_step v_prev v_next
| deposit_step id qty :
  deposit id qty v_prev = v_next →
  vault_step v_prev v_next
| withdraw_step id qty :
  withdraw id qty v_prev = Except.ok v_next →
  vault_step v_prev v_next
| create_step id :
  acct_create id v_prev = Except.ok v_next →
  vault_step v_prev v_next
| destroy_step id :
  acct_destroy id v_prev = Except.ok v_next →
  vault_step v_prev v_next

-- trace
inductive vault_trace : Vault → Vault → Prop
| clnil : ∀ x,
    vault_trace x x
| snoc : ∀ frm mid to,
    vault_trace frm mid →
    vault_step  mid to →
    vault_trace frm to

-- reachable
def reachable_vault (v : Vault) : Prop :=
  ∃ (_ : vault_trace init_vault v), True

-- INVARIANTS
-- invariant: balance equals deposits + transfers_to - withdraws - transfers_from
