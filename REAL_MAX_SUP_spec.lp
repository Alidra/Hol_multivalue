require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5203039 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_max x y) (sup ((@INSERT real) x ((@INSERT real) y (@EMPTY real)))))))));
