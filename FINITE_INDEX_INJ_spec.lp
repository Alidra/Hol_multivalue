require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7612100 [A] : Prf (∀ (λ i : El num, (∀ (λ j : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (∧ (<= i ((@dimindex A) (@UNIV A))) (∧ (<= (NUMERAL (BIT1 _0)) j) (<= j ((@dimindex A) (@UNIV A)))))) (= (= ((@finite_index A) i) ((@finite_index A) j)) (= i j)))))));
