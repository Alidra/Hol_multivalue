require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7586372 : Prf (∀ (λ P : El (fun (fun real real) bool), (⇒ (∧ (P (λ x : El real, x)) (∧ (∀ (λ c : El real, (P (λ x : El real, c)))) (∧ (∀ (λ p : El (fun real real), (∀ (λ q : El (fun real real), (⇒ (∧ (P p) (P q)) (P (λ x : El real, (real_add (p x) (q x))))))))) (∀ (λ p : El (fun real real), (∀ (λ q : El (fun real real), (⇒ (∧ (P p) (P q)) (P (λ x : El real, (real_mul (p x) (q x)))))))))))) (∀ (λ p : El (fun real real), (⇒ (polynomial_function p) (P p)))))));
