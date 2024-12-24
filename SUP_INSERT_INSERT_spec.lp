require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5180944 : Prf (∀ (λ a : El real, (∀ (λ b : El real, (∀ (λ s : El (fun real bool), (= (sup ((@INSERT real) b ((@INSERT real) a s))) (sup ((@INSERT real) (real_max a b) s)))))))));
