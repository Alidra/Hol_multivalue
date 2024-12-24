require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7919632 [A B] : Prf (∧ (∀ (λ a : El (finite_prod A B), (= ((@mk_finite_prod A B) ((@dest_finite_prod A B) a)) a))) (∀ (λ r : El num, (= ((@IN num) r (… (NUMERAL (BIT1 _0)) (* ((@dimindex A) (@UNIV A)) ((@dimindex B) (@UNIV B))))) (= ((@dest_finite_prod A B) ((@mk_finite_prod A B) r)) r)))));
