require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7643282 [A M N] : Prf (∀ (λ x : El (cart A M), (∀ (λ y : El (cart A N), (= ((@fstcart A M N) ((@pastecart A M N) x y)) x)))));
