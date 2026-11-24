theorem excludedMiddleDemo (P : Prop) : P ∨ ¬ P :=      -- 排中律：P成立或P不成立
  Classical.em P                                        -- 使用经典排中律证明 P 或非 P

#print axioms excludedMiddleDemo
