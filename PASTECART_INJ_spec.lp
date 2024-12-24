require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7664494 [A M N] : Prf (∀ (λ x : El (cart A M), (∀ (λ y : El (cart A N), (∀ (λ w : El (cart A M), (∀ (λ z : El (cart A N), (= (= ((@pastecart A M N) x y) ((@pastecart A M N) w z)) (∧ (= x w) (= y z)))))))))));
