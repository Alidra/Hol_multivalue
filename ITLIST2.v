Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITLIST2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1108213_spec.
Require Import thm1108214_spec.
Require Import thm1108228_spec.
Require Import thm1108229_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1108239 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) (b : _25645) : (@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2 b) = b.
Proof. exact (EQ_MP (@lem1108214 _25645 _25647 _25655 f l2 b) (@lem1108213 _25645 _25647 _25655 f l2 b)). Qed.
Lemma lem1108240 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (l2 : list _25688) (b : _25687) : (@ITLIST2 _25687 _25689 _25688 f (@nil _25689) l2 b) = b.
Proof. exact (@lem1108239 _25687 _25689 _25688 f l2 b). Qed.
Lemma lem1108241 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (b : _25687) : (@ITLIST2 _25687 _25689 _25688 f (@nil _25689) (@nil _25688) b) = b.
Proof. exact (@lem1108240 _25687 _25688 _25689 f (@nil _25688) b). Qed.
Lemma lem1108242 {_25687 : Type'} : (@eq _25687) = (@eq _25687).
Proof. exact (eq_refl (@eq _25687)). Qed.
Lemma lem1108243 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (b : _25687) : (term0 _25687 _25688 _25689 f b) = (@eq _25687 b).
Proof. exact (MK_COMB (@lem1108242 _25687) (@lem1108241 _25687 _25688 _25689 f b)). Qed.
Lemma lem1108244 {_25687 : Type'} (b : _25687) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1108245 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (b : _25687) : ((@ITLIST2 _25687 _25689 _25688 f (@nil _25689) (@nil _25688) b) = b) = (b = b).
Proof. exact (MK_COMB (@lem1108243 _25687 _25688 _25689 f b) (@lem1108244 _25687 b)). Qed.
Lemma lem1108247 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1108248 {_25687 : Type'} (x : _25687) : (x = x) = True.
Proof. exact (@lem1108247 _25687 x). Qed.
Lemma lem1108249 {_25687 : Type'} (b : _25687) : (b = b) = True.
Proof. exact (@lem1108248 _25687 b). Qed.
Lemma lem1108250 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (b : _25687) : ((@ITLIST2 _25687 _25689 _25688 f (@nil _25689) (@nil _25688) b) = b) = True.
Proof. exact (TRANS (@lem1108245 _25687 _25688 _25689 f b) (@lem1108249 _25687 b)). Qed.
Lemma lem1108251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1108252 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (b : _25687) : (term1 _25687 _25688 _25689 f b) = (and True).
Proof. exact (MK_COMB (@lem1108251) (@lem1108250 _25687 _25688 _25689 f b)). Qed.
Lemma lem1108256 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) (b : _25645) : (term2 _25645 _25647 _25655 f h1' t1 l2 b) = (term3 _25645 _25647 _25655 h1' f t1 l2 b).
Proof. exact (EQ_MP (@lem1108229 _25645 _25647 _25655 h1' f t1 l2 b) (@lem1108228 _25645 _25647 _25655 h1' f t1 l2 b)). Qed.
Lemma lem1108257 {_25687 _25688 _25689 : Type'} (h1' : _25689) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (l2 : list _25688) (b : _25687) : (term4 _25687 _25688 _25689 f h1' t1 l2 b) = (term5 _25687 _25688 _25689 h1' f t1 l2 b).
Proof. exact (@lem1108256 _25687 _25689 _25688 h1' f t1 l2 b). Qed.
Lemma lem1108258 {_25687 _25688 _25689 : Type'} (h1' : _25689) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (h2' : _25688) (t2 : list _25688) (b : _25687) : (term6 _25687 _25688 _25689 f h1' t1 h2' t2 b) = (term7 _25687 _25688 _25689 h1' f t1 h2' t2 b).
Proof. exact (@lem1108257 _25687 _25688 _25689 h1' f t1 (@cons _25688 h2' t2) b). Qed.
Lemma lem1108260 {A : Type'} (t : list A) (h : A) : (term8 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1108261 {_25688 : Type'} (t : list _25688) (h : _25688) : (term8 _25688 h t) = h.
Proof. exact (@lem1108260 _25688 t h). Qed.
Lemma lem1108262 {_25688 : Type'} (t2 : list _25688) (h2' : _25688) : (term8 _25688 h2' t2) = h2'.
Proof. exact (@lem1108261 _25688 t2 h2'). Qed.
Lemma lem1108263 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (h1' : _25689) : (f h1') = (f h1').
Proof. exact (eq_refl (f h1')). Qed.
Lemma lem1108264 {_25687 _25688 _25689 : Type'} (t2 : list _25688) (f : type1515 _25687 _25688 _25689) (h1' : _25689) (h2' : _25688) : (term9 _25687 _25688 _25689 f h1' h2' t2) = (f h1' h2').
Proof. exact (MK_COMB (@lem1108263 _25687 _25688 _25689 f h1') (@lem1108262 _25688 t2 h2')). Qed.
Lemma lem1108266 {A : Type'} (h : A) (t : list A) : (term10 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1108267 {_25688 : Type'} (h : _25688) (t : list _25688) : (term10 _25688 h t) = t.
Proof. exact (@lem1108266 _25688 h t). Qed.
Lemma lem1108268 {_25688 : Type'} (h2' : _25688) (t2 : list _25688) : (term10 _25688 h2' t2) = t2.
Proof. exact (@lem1108267 _25688 h2' t2). Qed.
Lemma lem1108269 {_25687 _25688 _25689 : Type'} (f : type1515 _25687 _25688 _25689) (t1 : list _25689) : (@ITLIST2 _25687 _25689 _25688 f t1) = (@ITLIST2 _25687 _25689 _25688 f t1).
Proof. exact (eq_refl (@ITLIST2 _25687 _25689 _25688 f t1)). Qed.
Lemma lem1108270 {_25687 _25688 _25689 : Type'} (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) : (term11 _25687 _25688 _25689 f t1 h2' t2) = (@ITLIST2 _25687 _25689 _25688 f t1 t2).
Proof. exact (MK_COMB (@lem1108269 _25687 _25688 _25689 f t1) (@lem1108268 _25688 h2' t2)). Qed.
Lemma lem1108271 {_25687 : Type'} (b : _25687) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1108272 {_25687 _25688 _25689 : Type'} (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : (term12 _25687 _25688 _25689 f t1 h2' t2 b) = (@ITLIST2 _25687 _25689 _25688 f t1 t2 b).
Proof. exact (MK_COMB (@lem1108270 _25687 _25688 _25689 h2' f t1 t2) (@lem1108271 _25687 b)). Qed.
Lemma lem1108273 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : (term7 _25687 _25688 _25689 h1' f t1 h2' t2 b) = (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b).
Proof. exact (MK_COMB (@lem1108264 _25687 _25688 _25689 t2 f h1' h2') (@lem1108272 _25687 _25688 _25689 h2' f t1 t2 b)). Qed.
Lemma lem1108274 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : (term6 _25687 _25688 _25689 f h1' t1 h2' t2 b) = (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b).
Proof. exact (TRANS (@lem1108258 _25687 _25688 _25689 h1' f t1 h2' t2 b) (@lem1108273 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108275 {_25687 : Type'} : (@eq _25687) = (@eq _25687).
Proof. exact (eq_refl (@eq _25687)). Qed.
Lemma lem1108276 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : (term14 _25687 _25688 _25689 f h1' t1 h2' t2 b) = (term15 _25687 _25688 _25689 h1' h2' f t1 t2 b).
Proof. exact (MK_COMB (@lem1108275 _25687) (@lem1108274 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108277 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b) = (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b).
Proof. exact (eq_refl (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108278 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : ((term6 _25687 _25688 _25689 f h1' t1 h2' t2 b) = (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b)) = ((term13 _25687 _25688 _25689 h1' h2' f t1 t2 b) = (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b)).
Proof. exact (MK_COMB (@lem1108276 _25687 _25688 _25689 h1' h2' f t1 t2 b) (@lem1108277 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108280 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1108281 {_25687 : Type'} (x : _25687) : (x = x) = True.
Proof. exact (@lem1108280 _25687 x). Qed.
Lemma lem1108282 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : ((term13 _25687 _25688 _25689 h1' h2' f t1 t2 b) = (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b)) = True.
Proof. exact (@lem1108281 _25687 (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108283 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : ((term6 _25687 _25688 _25689 f h1' t1 h2' t2 b) = (term13 _25687 _25688 _25689 h1' h2' f t1 t2 b)) = True.
Proof. exact (TRANS (@lem1108278 _25687 _25688 _25689 h1' h2' f t1 t2 b) (@lem1108282 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108284 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : (term16 _25687 _25688 _25689 h1' h2' f t1 t2 b) = (True /\ True).
Proof. exact (MK_COMB (@lem1108252 _25687 _25688 _25689 f b) (@lem1108283 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108286 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1108287 : (True /\ True) = True.
Proof. exact (@lem1108286 True). Qed.
Lemma lem1108288 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : (term16 _25687 _25688 _25689 h1' h2' f t1 t2 b) = True.
Proof. exact (TRANS (@lem1108284 _25687 _25688 _25689 h1' h2' f t1 t2 b) (@lem1108287)). Qed.
Lemma lem1108289 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : True = (term16 _25687 _25688 _25689 h1' h2' f t1 t2 b).
Proof. exact (SYM (@lem1108288 _25687 _25688 _25689 h1' h2' f t1 t2 b)). Qed.
Lemma lem1108290 {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : type1515 _25687 _25688 _25689) (t1 : list _25689) (t2 : list _25688) (b : _25687) : term16 _25687 _25688 _25689 h1' h2' f t1 t2 b.
Proof. exact (EQ_MP (@lem1108289 _25687 _25688 _25689 h1' h2' f t1 t2 b) (@lem0)). Qed.
