require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7614824 [N] (P : El (fun (finite_image N) bool)) : Prf (= (∀ (λ k : El (finite_image N), (P k))) (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex N) (@UNIV N)))) (P ((@finite_index N) i))))));
