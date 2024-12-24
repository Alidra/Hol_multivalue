require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7142723 [_133668] : Prf (∀ (λ s : El (fun _133668 bool), (∀ (λ f : El (fun _133668 real), (∀ (λ b : El real, (⇒ (∧ ((@FINITE _133668) s) (∧ (¬ (= s (@EMPTY _133668))) (∀ (λ x : El _133668, (⇒ ((@IN _133668) x s) (real_lt (f x) b)))))) (real_lt ((@sum _133668) s f) (real_mul (real_of_num ((@CARD _133668) s)) b)))))))));
