require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066938 [A B] (sum' : El (fun (recspace (prod A B)) bool)) (INL' : El (fun A (recspace (prod A B)))) (INR' : El (fun B (recspace (prod A B)))) (h1 : Prf (= sum' (λ a : El (recspace (prod A B)), (∀ (λ sum'' : El (fun (recspace (prod A B)) bool), (⇒ (∀ (λ a' : El (recspace (prod A B)), (⇒ (∨ (∃ (λ a'' : El A, (= a' (INL' a'')))) (∃ (λ a'' : El B, (= a' (INR' a''))))) (sum'' a')))) (sum'' a))))))) : Prf (∧ (∀ (λ a : El A, (sum' (INL' a)))) (∀ (λ a : El B, (sum' (INR' a)))));
