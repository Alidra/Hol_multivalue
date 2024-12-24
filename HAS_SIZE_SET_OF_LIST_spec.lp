require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4907451 [_112866] : Prf (∀ (λ l : El (list _112866), (= ((@HAS_SIZE _112866) ((@set_of_list _112866) l) ((@LENGTH _112866) l)) ((@PAIRWISE _112866) (λ x : El _112866, (λ y : El _112866, (¬ (= x y)))) l))));
