require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7635254 [A M N] : Prf (∀ (λ f : El (cart A (finite_sum M N)), (= ((@sndcart A M N) f) ((@lambda A N) (λ i : El num, ((@﹩ A (finite_sum M N)) f (+ i ((@dimindex M) (@UNIV M)))))))));
