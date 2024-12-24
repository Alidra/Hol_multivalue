require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7603491 [A] : Prf (∧ (∀ (λ a : El (finite_image A), (= ((@finite_index A) ((@dest_finite_image A) a)) a))) (∀ (λ r : El num, (= ((@IN num) r (… (NUMERAL (BIT1 _0)) ((@dimindex A) (@UNIV A)))) (= ((@dest_finite_image A) ((@finite_index A) r)) r)))));
