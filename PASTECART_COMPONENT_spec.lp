require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7670352 [A M N] : Prf (∧ (∀ (λ u : El (cart A M), (∀ (λ v : El (cart A N), (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex M) (@UNIV M)))) (= ((@﹩ A (finite_sum M N)) ((@pastecart A M N) u v) i) ((@﹩ A M) u i))))))))) (∀ (λ u : El (cart A M), (∀ (λ v : El (cart A N), (∀ (λ i : El num, (⇒ (∧ (<= (+ ((@dimindex M) (@UNIV M)) (NUMERAL (BIT1 _0))) i) (<= i (+ ((@dimindex M) (@UNIV M)) ((@dimindex N) (@UNIV N))))) (= ((@﹩ A (finite_sum M N)) ((@pastecart A M N) u v) i) ((@﹩ A N) v (- i ((@dimindex M) (@UNIV M)))))))))))));
