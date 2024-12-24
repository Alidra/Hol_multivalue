require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7604549 [A] : Prf (∀ (λ x : El (finite_image A), (∃ (λ x' : El num, (∧ (= x ((@finite_index A) x')) ((@IN num) x' (… (NUMERAL (BIT1 _0)) ((@dimindex A) (@UNIV A)))))))));
