require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7077564 [_132203] : Prf (∀ (λ f : El (fun _132203 real), (∀ (λ g : El (fun _132203 real), (∀ (λ s : El (fun _132203 bool), (⇒ (∧ ((@FINITE _132203) s) (∧ (¬ (= s (@EMPTY _132203))) (∀ (λ x : El _132203, (⇒ ((@IN _132203) x s) (real_lt (f x) (g x))))))) (real_lt ((@sum _132203) s f) ((@sum _132203) s g)))))))));
