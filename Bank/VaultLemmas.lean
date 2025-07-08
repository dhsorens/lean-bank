import Bank.Vault

axiom rbmap_insert_find : ∀ (m : Map Nat Nat compare) k v,
  (Lean.RBMap.insert m k v).findD k 0 =
  v

axiom rbmap_insert_findD : ∀ (m : Map Nat Nat compare) k v,
  (Lean.RBMap.insert m k v).findD k 0 =
  v

axiom rbmap_insert_find_neq : ∀ (m : Map Nat Nat compare) k k',
  ¬k' = k →
  (Lean.RBMap.insert m k 0).findD k' 0 = Lean.RBMap.findD m k' 0

axiom rbmap_erase_find_neq : ∀ (m : Map Nat Nat compare) (k k' : Nat), ¬k' = k → (Lean.RBMap.erase m k).findD k' 0 = Lean.RBMap.findD m k' 0
