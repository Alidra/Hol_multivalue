require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5753565 [_120477 _120519 _120521] : Prf (∀ (λ op : El (fun _120519 (fun _120519 _120519)), (⇒ ((@monoidal _120519) op) (∧ (∀ (λ f : El (fun _120477 _120519), (= ((@iterate _120519 _120477) op (@EMPTY _120477) f) ((@neutral _120519) op)))) (∀ (λ f : El (fun _120521 _120519), (∀ (λ x : El _120521, (∀ (λ s : El (fun _120521 bool), (⇒ ((@FINITE _120521) s) (= ((@iterate _120519 _120521) op ((@INSERT _120521) x s) f) ((@COND _120519) ((@IN _120521) x s) ((@iterate _120519 _120521) op s f) (op (f x) ((@iterate _120519 _120521) op s f)))))))))))))));
