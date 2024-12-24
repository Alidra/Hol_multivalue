require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7609879 [A] : Prf (∀ (λ i : El (finite_image A), ((@∃! num) (λ n : El num, (∧ (<= (NUMERAL (BIT1 _0)) n) (∧ (<= n ((@dimindex A) (@UNIV A))) (= ((@finite_index A) n) i)))))));
