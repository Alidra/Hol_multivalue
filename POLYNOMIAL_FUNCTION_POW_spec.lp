require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7581930 : Prf (∀ (λ p : El (fun real real), (∀ (λ n : El num, (⇒ (polynomial_function p) (polynomial_function (λ x : El real, (real_pow (p x) n))))))));
