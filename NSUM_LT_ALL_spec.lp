require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6938734 [_127128] : Prf (∀ (λ f : El (fun _127128 num), (∀ (λ g : El (fun _127128 num), (∀ (λ s : El (fun _127128 bool), (⇒ (∧ ((@FINITE _127128) s) (∧ (¬ (= s (@EMPTY _127128))) (∀ (λ x : El _127128, (⇒ ((@IN _127128) x s) (< (f x) (g x))))))) (< ((@nsum _127128) s f) ((@nsum _127128) s g)))))))));
