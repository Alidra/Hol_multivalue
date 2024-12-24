require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7629993 [A N] : Prf (∀ (λ x : El (cart A N), (∀ (λ y : El (cart A N), (= (= x y) (∀ (λ i : El num, (= ((@﹩ A N) x i) ((@﹩ A N) y i)))))))));
