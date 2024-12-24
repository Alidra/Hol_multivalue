require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7664619 [A M N] : Prf (∀ (λ x : El (cart A (finite_sum M N)), (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex M) (@UNIV M)))) (= ((@﹩ A M) ((@fstcart A M N) x) i) ((@﹩ A (finite_sum M N)) x i)))))));
