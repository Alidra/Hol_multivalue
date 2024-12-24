require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7199888 [A] : Prf (∀ (λ P : El (fun real bool), (∀ (λ f : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ (P (real_of_num (NUMERAL _0))) (∧ (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (P x) (P y)) (P (real_add x y))))))) (∀ (λ a : El A, (⇒ ((@IN A) a s) (P (f a))))))) (P ((@sum A) s f)))))))));
