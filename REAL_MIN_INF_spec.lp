require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5288764 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_min x y) (inf ((@INSERT real) x ((@INSERT real) y (@EMPTY real)))))))));
