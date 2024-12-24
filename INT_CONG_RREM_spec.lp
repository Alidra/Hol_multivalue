require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2528300 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ n : El int, (= ((@== int) x (rem y n) (int_mod n)) ((@== int) x y (int_mod n)))))))));
