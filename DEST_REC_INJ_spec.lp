require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1059772 [A] : Prf (∀ (λ x : El (recspace A), (∀ (λ y : El (recspace A), (= (= ((@_dest_rec A) x) ((@_dest_rec A) y)) (= x y))))));
