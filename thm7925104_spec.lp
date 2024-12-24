require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7925104 [A] (a : El (finite_sum A A)) (tybit0' : El (fun (recspace (finite_sum A A)) bool)) (_103783' : El (fun (finite_sum A A) (recspace (finite_sum A A)))) (h1 : Prf (= tybit0' (λ a' : El (recspace (finite_sum A A)), (∀ (λ tybit0'' : El (fun (recspace (finite_sum A A)) bool), (⇒ (∀ (λ a'' : El (recspace (finite_sum A A)), (⇒ (∃ (λ a''' : El (finite_sum A A), (= a'' (_103783' a''')))) (tybit0'' a'')))) (tybit0'' a'))))))) : Prf (tybit0' (_103783' a));
