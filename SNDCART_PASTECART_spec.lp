require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7648197 [A M N] : Prf (∀ (λ x : El (cart A M), (∀ (λ y : El (cart A N), (= ((@sndcart A M N) ((@pastecart A M N) x y)) y)))));
