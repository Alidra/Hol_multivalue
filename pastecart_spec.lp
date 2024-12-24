require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7632649 [A M N] : Prf (∀ (λ f : El (cart A M), (∀ (λ g : El (cart A N), (= ((@pastecart A M N) f g) ((@lambda A (finite_sum M N)) (λ i : El num, ((@COND A) (<= i ((@dimindex M) (@UNIV M))) ((@﹩ A M) f i) ((@﹩ A N) g (- i ((@dimindex M) (@UNIV M))))))))))));
