namespace FilterCalculus

def above (cutoff n : Nat) : Prop := cutoff ≤ n

theorem above_self (n : Nat) : above n n := by          -- 每个自然数都不小于自身
  exact Nat.le_refl n

end FilterCalculus
