require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7567525 : Prf (∀ (λ p : El (fun real real), (∀ (λ c : El real, (⇒ (polynomial_function p) (polynomial_function (λ x : El real, (real_mul c (p x)))))))));
