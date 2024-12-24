require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7577427 : Prf (∀ (λ p : El (fun real real), (∀ (λ q : El (fun real real), (⇒ (∧ (polynomial_function p) (polynomial_function q)) (polynomial_function (λ x : El real, (real_mul (p x) (q x)))))))));
