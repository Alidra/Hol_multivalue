require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7631335 [A B] : Prf (∧ (∀ (λ a : El (finite_sum A B), (= ((@mk_finite_sum A B) ((@dest_finite_sum A B) a)) a))) (∀ (λ r : El num, (= ((@IN num) r (… (NUMERAL (BIT1 _0)) (+ ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))))) (= ((@dest_finite_sum A B) ((@mk_finite_sum A B) r)) r)))));
