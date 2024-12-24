require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1338093 : Prf (∧ (∀ (λ x : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (= (treal_eq x y) (= (mk_real (treal_eq x)) (mk_real (treal_eq y)))))))) (∧ (∀ (λ P : El (fun real bool), (= (∀ (λ x : El (prod hreal hreal), (P (mk_real (treal_eq x))))) (∀ (λ x : El real, (P x)))))) (∧ (∀ (λ P : El (fun real bool), (= (∃ (λ x : El (prod hreal hreal), (P (mk_real (treal_eq x))))) (∃ (λ x : El real, (P x)))))) (∀ (λ x : El real, (= (mk_real (treal_eq ((@ε (prod hreal hreal)) (dest_real x)))) x))))));
