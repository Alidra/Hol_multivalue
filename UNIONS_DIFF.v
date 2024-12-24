Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_DIFF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Lemma lem3473274 {_89520 _89534 : Type'} : term0 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem3473275 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term1 _89520 _89534 P.
Proof. exact (@lem3473274 _89520 _89534 P). Qed.
Lemma lem3473276 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term1 _89520 _89534 P) = (term2 _89520 _89534 P).
Proof. exact (eq_refl (term1 _89520 _89534 P)). Qed.
Lemma lem3473277 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term2 _89520 _89534 P.
Proof. exact (EQ_MP (@lem3473276 _89520 _89534 P) (@lem3473275 _89520 _89534 P)). Qed.
Lemma lem3473278 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term3 _89520 _89534 P f.
Proof. exact (@lem3473277 _89520 _89534 P f). Qed.
Lemma lem3473279 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term3 _89520 _89534 P f) = ((term4 _89520 _89534 P f) = (term5 _89520 _89534 P f)).
Proof. exact (eq_refl (term3 _89520 _89534 P f)). Qed.
Lemma lem3473292 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term4 _89520 _89534 P f) = (term5 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem3473279 _89520 _89534 P f) (@lem3473278 _89520 _89534 P f)). Qed.
Lemma lem3473293 {_90144 : Type'} (P : type686 _90144) (f : type672 _90144) : (term6 _90144 P f) = (term7 _90144 P f).
Proof. exact (@lem3473292 _90144 (_90144 -> Prop) P f). Qed.
Lemma lem3473294 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term8 _90144 s t) = (term9 _90144 s t).
Proof. exact (@lem3473293 _90144 (term10 _90144 s) (term11 _90144 t)). Qed.
Lemma lem3473295 {_90144 : Type'} (x : _90144 -> Prop) (s : type686 _90144) : (term12 _90144 s x) = (@IN (_90144 -> Prop) x s).
Proof. exact (eq_refl (term12 _90144 s x)). Qed.
Lemma lem3473296 {_90144 : Type'} (GEN_PVAR_67 : _90144 -> Prop) : (@SETSPEC (_90144 -> Prop) GEN_PVAR_67) = (@SETSPEC (_90144 -> Prop) GEN_PVAR_67).
Proof. exact (eq_refl (@SETSPEC (_90144 -> Prop) GEN_PVAR_67)). Qed.
Lemma lem3473297 {_90144 : Type'} (GEN_PVAR_67 : _90144 -> Prop) (x : _90144 -> Prop) (s : type686 _90144) : (term13 _90144 GEN_PVAR_67 s x) = (term14 _90144 GEN_PVAR_67 x s).
Proof. exact (MK_COMB (@lem3473296 _90144 GEN_PVAR_67) (@lem3473295 _90144 x s)). Qed.
Lemma lem3473298 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) : (term15 _90144 t x) = (@DIFF _90144 x t).
Proof. exact (eq_refl (term15 _90144 t x)). Qed.
Lemma lem3473299 {_90144 : Type'} (GEN_PVAR_67 : _90144 -> Prop) (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) : (term16 _90144 GEN_PVAR_67 s t x) = (term17 _90144 GEN_PVAR_67 s x t).
Proof. exact (MK_COMB (@lem3473297 _90144 GEN_PVAR_67 x s) (@lem3473298 _90144 x t)). Qed.
Lemma lem3473300 {_90144 : Type'} (GEN_PVAR_67 : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) : (term18 _90144 GEN_PVAR_67 s t) = (term19 _90144 GEN_PVAR_67 s t).
Proof. exact (fun_ext (fun x : _90144 -> Prop => @lem3473299 _90144 GEN_PVAR_67 s x t)). Qed.
Lemma lem3473301 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473302 {_90144 : Type'} (GEN_PVAR_67 : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) : (term20 _90144 GEN_PVAR_67 s t) = (term21 _90144 GEN_PVAR_67 s t).
Proof. exact (MK_COMB (@lem3473301 _90144) (@lem3473300 _90144 GEN_PVAR_67 s t)). Qed.
Lemma lem3473303 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term22 _90144 s t) = (term23 _90144 s t).
Proof. exact (fun_ext (fun GEN_PVAR_67 : _90144 -> Prop => @lem3473302 _90144 GEN_PVAR_67 s t)). Qed.
Lemma lem3473304 {_90144 : Type'} : (@GSPEC (_90144 -> Prop)) = (@GSPEC (_90144 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_90144 -> Prop))). Qed.
Lemma lem3473305 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term24 _90144 s t) = (term25 _90144 s t).
Proof. exact (MK_COMB (@lem3473304 _90144) (@lem3473303 _90144 s t)). Qed.
Lemma lem3473306 {_90144 : Type'} : (@UNIONS _90144) = (@UNIONS _90144).
Proof. exact (eq_refl (@UNIONS _90144)). Qed.
Lemma lem3473307 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term8 _90144 s t) = (term26 _90144 s t).
Proof. exact (MK_COMB (@lem3473306 _90144) (@lem3473305 _90144 s t)). Qed.
Lemma lem3473308 {_90144 : Type'} : (@eq (_90144 -> Prop)) = (@eq (_90144 -> Prop)).
Proof. exact (eq_refl (@eq (_90144 -> Prop))). Qed.
Lemma lem3473309 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term27 _90144 s t) = (term28 _90144 s t).
Proof. exact (MK_COMB (@lem3473308 _90144) (@lem3473307 _90144 s t)). Qed.
Lemma lem3473310 {_90144 : Type'} (x : _90144 -> Prop) (s : type686 _90144) : (term12 _90144 s x) = (@IN (_90144 -> Prop) x s).
Proof. exact (eq_refl (term12 _90144 s x)). Qed.
Lemma lem3473311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473312 {_90144 : Type'} (x : _90144 -> Prop) (s : type686 _90144) : (term29 _90144 s x) = (term30 _90144 x s).
Proof. exact (MK_COMB (@lem3473311) (@lem3473310 _90144 x s)). Qed.
Lemma lem3473313 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) : (term15 _90144 t x) = (@DIFF _90144 x t).
Proof. exact (eq_refl (term15 _90144 t x)). Qed.
Lemma lem3473314 {_90144 : Type'} (a : _90144) : (@IN _90144 a) = (@IN _90144 a).
Proof. exact (eq_refl (@IN _90144 a)). Qed.
Lemma lem3473315 {_90144 : Type'} (a : _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) : (term31 _90144 a t x) = (term32 _90144 a x t).
Proof. exact (MK_COMB (@lem3473314 _90144 a) (@lem3473313 _90144 x t)). Qed.
Lemma lem3473316 {_90144 : Type'} (s : type686 _90144) (a : _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) : (term33 _90144 s a t x) = (term34 _90144 s a x t).
Proof. exact (MK_COMB (@lem3473312 _90144 x s) (@lem3473315 _90144 a x t)). Qed.
Lemma lem3473317 {_90144 : Type'} (s : type686 _90144) (a : _90144) (t : _90144 -> Prop) : (term35 _90144 s a t) = (term36 _90144 s a t).
Proof. exact (fun_ext (fun x : _90144 -> Prop => @lem3473316 _90144 s a x t)). Qed.
Lemma lem3473318 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473319 {_90144 : Type'} (s : type686 _90144) (a : _90144) (t : _90144 -> Prop) : (term37 _90144 s a t) = (term38 _90144 s a t).
Proof. exact (MK_COMB (@lem3473318 _90144) (@lem3473317 _90144 s a t)). Qed.
Lemma lem3473320 {_90144 : Type'} (GEN_PVAR_50 : _90144) : (@SETSPEC _90144 GEN_PVAR_50) = (@SETSPEC _90144 GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC _90144 GEN_PVAR_50)). Qed.
Lemma lem3473321 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (a : _90144) (t : _90144 -> Prop) : (term39 _90144 GEN_PVAR_50 s a t) = (term40 _90144 GEN_PVAR_50 s a t).
Proof. exact (MK_COMB (@lem3473320 _90144 GEN_PVAR_50) (@lem3473319 _90144 s a t)). Qed.
Lemma lem3473322 {_90144 : Type'} (a : _90144) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3473323 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (t : _90144 -> Prop) (a : _90144) : (term41 _90144 GEN_PVAR_50 s t a) = (term42 _90144 GEN_PVAR_50 s t a).
Proof. exact (MK_COMB (@lem3473321 _90144 GEN_PVAR_50 s a t) (@lem3473322 _90144 a)). Qed.
Lemma lem3473324 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (t : _90144 -> Prop) : (term43 _90144 GEN_PVAR_50 s t) = (term44 _90144 GEN_PVAR_50 s t).
Proof. exact (fun_ext (fun a : _90144 => @lem3473323 _90144 GEN_PVAR_50 s t a)). Qed.
Lemma lem3473325 {_90144 : Type'} : (@ex _90144) = (@ex _90144).
Proof. exact (eq_refl (@ex _90144)). Qed.
Lemma lem3473326 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (t : _90144 -> Prop) : (term45 _90144 GEN_PVAR_50 s t) = (term46 _90144 GEN_PVAR_50 s t).
Proof. exact (MK_COMB (@lem3473325 _90144) (@lem3473324 _90144 GEN_PVAR_50 s t)). Qed.
Lemma lem3473327 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term47 _90144 s t) = (term48 _90144 s t).
Proof. exact (fun_ext (fun GEN_PVAR_50 : _90144 => @lem3473326 _90144 GEN_PVAR_50 s t)). Qed.
Lemma lem3473328 {_90144 : Type'} : (@GSPEC _90144) = (@GSPEC _90144).
Proof. exact (eq_refl (@GSPEC _90144)). Qed.
Lemma lem3473329 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term9 _90144 s t) = (term49 _90144 s t).
Proof. exact (MK_COMB (@lem3473328 _90144) (@lem3473327 _90144 s t)). Qed.
Lemma lem3473330 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : ((term8 _90144 s t) = (term9 _90144 s t)) = ((term26 _90144 s t) = (term49 _90144 s t)).
Proof. exact (MK_COMB (@lem3473309 _90144 s t) (@lem3473329 _90144 s t)). Qed.
Lemma lem3473331 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term26 _90144 s t) = (term49 _90144 s t).
Proof. exact (EQ_MP (@lem3473330 _90144 s t) (@lem3473294 _90144 s t)). Qed.
Lemma lem3473342 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term50 _90144 s t) = (term50 _90144 s t).
Proof. exact (eq_refl (term50 _90144 s t)). Qed.
Lemma lem3473343 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : ((term51 _90144 s t) = (term26 _90144 s t)) = ((term51 _90144 s t) = (term49 _90144 s t)).
Proof. exact (MK_COMB (@lem3473342 _90144 s t) (@lem3473331 _90144 s t)). Qed.
Lemma lem3473346 {_90144 : Type'} (s : type686 _90144) : (term52 _90144 s) = (term53 _90144 s).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473343 _90144 s t)). Qed.
Lemma lem3473347 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3473348 {_90144 : Type'} (s : type686 _90144) : (term54 _90144 s) = (term55 _90144 s).
Proof. exact (MK_COMB (@lem3473347 _90144) (@lem3473346 _90144 s)). Qed.
Lemma lem3473353 {_90144 : Type'} : (term56 _90144) = (term57 _90144).
Proof. exact (fun_ext (fun s : type686 _90144 => @lem3473348 _90144 s)). Qed.
Lemma lem3473354 {_90144 : Type'} : (@all ((_90144 -> Prop) -> Prop)) = (@all ((_90144 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90144 -> Prop) -> Prop))). Qed.
Lemma lem3473355 {_90144 : Type'} : (term58 _90144) = (term59 _90144).
Proof. exact (MK_COMB (@lem3473354 _90144) (@lem3473353 _90144)). Qed.
Lemma lem3473360 {_90144 : Type'} : (term59 _90144) = (term58 _90144).
Proof. exact (SYM (@lem3473355 _90144)). Qed.
Lemma lem3473372 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term60 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3473373 {_90144 : Type'} (s : _90144 -> Prop) (t : _90144 -> Prop) : (s = t) = (term60 _90144 s t).
Proof. exact (@lem3473372 _90144 s t). Qed.
Lemma lem3473374 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : ((term51 _90144 s t) = (term49 _90144 s t)) = (term61 _90144 s t).
Proof. exact (@lem3473373 _90144 (term51 _90144 s t) (term49 _90144 s t)). Qed.
Lemma lem3473393 {_90144 : Type'} (s : type686 _90144) : (term53 _90144 s) = (term62 _90144 s).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473374 _90144 s t)). Qed.
Lemma lem3473394 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3473395 {_90144 : Type'} (s : type686 _90144) : (term55 _90144 s) = (term63 _90144 s).
Proof. exact (MK_COMB (@lem3473394 _90144) (@lem3473393 _90144 s)). Qed.
Lemma lem3473400 {_90144 : Type'} : (term57 _90144) = (term64 _90144).
Proof. exact (fun_ext (fun s : type686 _90144 => @lem3473395 _90144 s)). Qed.
Lemma lem3473401 {_90144 : Type'} : (@all ((_90144 -> Prop) -> Prop)) = (@all ((_90144 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90144 -> Prop) -> Prop))). Qed.
Lemma lem3473402 {_90144 : Type'} : (term59 _90144) = (term65 _90144).
Proof. exact (MK_COMB (@lem3473401 _90144) (@lem3473400 _90144)). Qed.
Lemma lem3473407 {_90144 : Type'} : (term65 _90144) = (term59 _90144).
Proof. exact (SYM (@lem3473402 _90144)). Qed.
Lemma lem3473423 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term66 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3473424 {_90144 : Type'} (s : _90144 -> Prop) (x : _90144) (t : _90144 -> Prop) : (term32 _90144 x s t) = (term66 _90144 s x t).
Proof. exact (@lem3473423 _90144 s x t). Qed.
Lemma lem3473425 {_90144 : Type'} (s : type686 _90144) (x : _90144) (t : _90144 -> Prop) : (term67 _90144 x s t) = (term68 _90144 s x t).
Proof. exact (@lem3473424 _90144 (@UNIONS _90144 s) x t). Qed.
Lemma lem3473429 {A : Type'} (s : type686 A) (x : A) : (term69 A x s) = (term70 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3473430 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term69 _90144 x s) = (term70 _90144 s x).
Proof. exact (@lem3473429 _90144 s x). Qed.
Lemma lem3473438 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3473439 {_90144 : Type'} (P : type686 _90144) (x : _90144 -> Prop) : (@IN (_90144 -> Prop) x P) = (P x).
Proof. exact (@lem3473438 (_90144 -> Prop) P x). Qed.
Lemma lem3473440 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (@IN (_90144 -> Prop) t s) = (s t).
Proof. exact (@lem3473439 _90144 s t). Qed.
Lemma lem3473441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473442 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term30 _90144 t s) = (term71 _90144 s t).
Proof. exact (MK_COMB (@lem3473441) (@lem3473440 _90144 s t)). Qed.
Lemma lem3473444 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3473445 {_90144 : Type'} (P : _90144 -> Prop) (x : _90144) : (@IN _90144 x P) = (P x).
Proof. exact (@lem3473444 _90144 P x). Qed.
Lemma lem3473446 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (@IN _90144 x t) = (t x).
Proof. exact (@lem3473445 _90144 t x). Qed.
Lemma lem3473447 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term72 _90144 s x t) = (term73 _90144 s t x).
Proof. exact (MK_COMB (@lem3473442 _90144 s t) (@lem3473446 _90144 t x)). Qed.
Lemma lem3473450 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term74 _90144 s x) = (term75 _90144 s x).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473447 _90144 s t x)). Qed.
Lemma lem3473451 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473452 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term70 _90144 s x) = (term76 _90144 s x).
Proof. exact (MK_COMB (@lem3473451 _90144) (@lem3473450 _90144 s x)). Qed.
Lemma lem3473457 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term69 _90144 x s) = (term76 _90144 s x).
Proof. exact (TRANS (@lem3473430 _90144 s x) (@lem3473452 _90144 s x)). Qed.
Lemma lem3473458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473459 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term77 _90144 x s) = (term78 _90144 s x).
Proof. exact (MK_COMB (@lem3473458) (@lem3473457 _90144 s x)). Qed.
Lemma lem3473461 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3473462 {_90144 : Type'} (P : _90144 -> Prop) (x : _90144) : (@IN _90144 x P) = (P x).
Proof. exact (@lem3473461 _90144 P x). Qed.
Lemma lem3473463 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (@IN _90144 x t) = (t x).
Proof. exact (@lem3473462 _90144 t x). Qed.
Lemma lem3473464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3473465 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term79 _90144 x t) = (term80 _90144 t x).
Proof. exact (MK_COMB (@lem3473464) (@lem3473463 _90144 t x)). Qed.
Lemma lem3473466 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term68 _90144 s x t) = (term81 _90144 s t x).
Proof. exact (MK_COMB (@lem3473459 _90144 s x) (@lem3473465 _90144 t x)). Qed.
Lemma lem3473469 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term67 _90144 x s t) = (term81 _90144 s t x).
Proof. exact (TRANS (@lem3473425 _90144 s x t) (@lem3473466 _90144 s t x)). Qed.
Lemma lem3473470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3473471 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term82 _90144 x s t) = (term83 _90144 s t x).
Proof. exact (MK_COMB (@lem3473470) (@lem3473469 _90144 s t x)). Qed.
Lemma lem3473473 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term84 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3473474 {_90144 : Type'} (p : _90144 -> Prop) (x : _90144) : (term84 _90144 x p) = (p x).
Proof. exact (@lem3473473 _90144 p x). Qed.
Lemma lem3473475 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term85 _90144 x s t) = (term86 _90144 s t x).
Proof. exact (@lem3473474 _90144 (term87 _90144 s t) x). Qed.
Lemma lem3473476 {_90144 : Type'} (s : type686 _90144) (a : _90144) (t : _90144 -> Prop) : (term86 _90144 s t a) = (term38 _90144 s a t).
Proof. exact (eq_refl (term86 _90144 s t a)). Qed.
Lemma lem3473477 {_90144 : Type'} (GEN_PVAR_50 : _90144) : (@SETSPEC _90144 GEN_PVAR_50) = (@SETSPEC _90144 GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC _90144 GEN_PVAR_50)). Qed.
Lemma lem3473478 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (a : _90144) (t : _90144 -> Prop) : (term88 _90144 GEN_PVAR_50 s t a) = (term40 _90144 GEN_PVAR_50 s a t).
Proof. exact (MK_COMB (@lem3473477 _90144 GEN_PVAR_50) (@lem3473476 _90144 s a t)). Qed.
Lemma lem3473479 {_90144 : Type'} (a : _90144) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3473480 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (t : _90144 -> Prop) (a : _90144) : (term89 _90144 GEN_PVAR_50 s t a) = (term42 _90144 GEN_PVAR_50 s t a).
Proof. exact (MK_COMB (@lem3473478 _90144 GEN_PVAR_50 s a t) (@lem3473479 _90144 a)). Qed.
Lemma lem3473481 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (t : _90144 -> Prop) : (term90 _90144 GEN_PVAR_50 s t) = (term44 _90144 GEN_PVAR_50 s t).
Proof. exact (fun_ext (fun a : _90144 => @lem3473480 _90144 GEN_PVAR_50 s t a)). Qed.
Lemma lem3473482 {_90144 : Type'} : (@ex _90144) = (@ex _90144).
Proof. exact (eq_refl (@ex _90144)). Qed.
Lemma lem3473483 {_90144 : Type'} (GEN_PVAR_50 : _90144) (s : type686 _90144) (t : _90144 -> Prop) : (term91 _90144 GEN_PVAR_50 s t) = (term46 _90144 GEN_PVAR_50 s t).
Proof. exact (MK_COMB (@lem3473482 _90144) (@lem3473481 _90144 GEN_PVAR_50 s t)). Qed.
Lemma lem3473484 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term92 _90144 s t) = (term48 _90144 s t).
Proof. exact (fun_ext (fun GEN_PVAR_50 : _90144 => @lem3473483 _90144 GEN_PVAR_50 s t)). Qed.
Lemma lem3473485 {_90144 : Type'} : (@GSPEC _90144) = (@GSPEC _90144).
Proof. exact (eq_refl (@GSPEC _90144)). Qed.
Lemma lem3473486 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term93 _90144 s t) = (term49 _90144 s t).
Proof. exact (MK_COMB (@lem3473485 _90144) (@lem3473484 _90144 s t)). Qed.
Lemma lem3473487 {_90144 : Type'} (x : _90144) : (@IN _90144 x) = (@IN _90144 x).
Proof. exact (eq_refl (@IN _90144 x)). Qed.
Lemma lem3473488 {_90144 : Type'} (x : _90144) (s : type686 _90144) (t : _90144 -> Prop) : (term85 _90144 x s t) = (term94 _90144 x s t).
Proof. exact (MK_COMB (@lem3473487 _90144 x) (@lem3473486 _90144 s t)). Qed.
Lemma lem3473489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3473490 {_90144 : Type'} (x : _90144) (s : type686 _90144) (t : _90144 -> Prop) : (term95 _90144 x s t) = (term96 _90144 x s t).
Proof. exact (MK_COMB (@lem3473489) (@lem3473488 _90144 x s t)). Qed.
Lemma lem3473491 {_90144 : Type'} (s : type686 _90144) (x : _90144) (t : _90144 -> Prop) : (term86 _90144 s t x) = (term38 _90144 s x t).
Proof. exact (eq_refl (term86 _90144 s t x)). Qed.
Lemma lem3473492 {_90144 : Type'} (s : type686 _90144) (x : _90144) (t : _90144 -> Prop) : ((term85 _90144 x s t) = (term86 _90144 s t x)) = ((term94 _90144 x s t) = (term38 _90144 s x t)).
Proof. exact (MK_COMB (@lem3473490 _90144 x s t) (@lem3473491 _90144 s x t)). Qed.
Lemma lem3473493 {_90144 : Type'} (s : type686 _90144) (x : _90144) (t : _90144 -> Prop) : (term94 _90144 x s t) = (term38 _90144 s x t).
Proof. exact (EQ_MP (@lem3473492 _90144 s x t) (@lem3473475 _90144 s t x)). Qed.
Lemma lem3473501 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3473502 {_90144 : Type'} (P : type686 _90144) (x : _90144 -> Prop) : (@IN (_90144 -> Prop) x P) = (P x).
Proof. exact (@lem3473501 (_90144 -> Prop) P x). Qed.
Lemma lem3473503 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) : (@IN (_90144 -> Prop) x s) = (s x).
Proof. exact (@lem3473502 _90144 s x). Qed.
Lemma lem3473504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473505 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) : (term30 _90144 x s) = (term71 _90144 s x).
Proof. exact (MK_COMB (@lem3473504) (@lem3473503 _90144 s x)). Qed.
Lemma lem3473507 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term66 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3473508 {_90144 : Type'} (s : _90144 -> Prop) (x : _90144) (t : _90144 -> Prop) : (term32 _90144 x s t) = (term66 _90144 s x t).
Proof. exact (@lem3473507 _90144 s x t). Qed.
Lemma lem3473509 {_90144 : Type'} (x : _90144 -> Prop) (x' : _90144) (t : _90144 -> Prop) : (term32 _90144 x' x t) = (term66 _90144 x x' t).
Proof. exact (@lem3473508 _90144 x x' t). Qed.
Lemma lem3473513 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3473514 {_90144 : Type'} (P : _90144 -> Prop) (x : _90144) : (@IN _90144 x P) = (P x).
Proof. exact (@lem3473513 _90144 P x). Qed.
Lemma lem3473515 {_90144 : Type'} (x : _90144 -> Prop) (x' : _90144) : (@IN _90144 x' x) = (x x').
Proof. exact (@lem3473514 _90144 x x'). Qed.
Lemma lem3473516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473517 {_90144 : Type'} (x : _90144 -> Prop) (x' : _90144) : (term97 _90144 x' x) = (term98 _90144 x x').
Proof. exact (MK_COMB (@lem3473516) (@lem3473515 _90144 x x')). Qed.
Lemma lem3473519 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3473520 {_90144 : Type'} (P : _90144 -> Prop) (x : _90144) : (@IN _90144 x P) = (P x).
Proof. exact (@lem3473519 _90144 P x). Qed.
Lemma lem3473521 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (@IN _90144 x t) = (t x).
Proof. exact (@lem3473520 _90144 t x). Qed.
Lemma lem3473522 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3473523 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term79 _90144 x t) = (term80 _90144 t x).
Proof. exact (MK_COMB (@lem3473522) (@lem3473521 _90144 t x)). Qed.
Lemma lem3473524 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term66 _90144 x x' t) = (term99 _90144 x t x').
Proof. exact (MK_COMB (@lem3473517 _90144 x x') (@lem3473523 _90144 t x')). Qed.
Lemma lem3473527 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term32 _90144 x' x t) = (term99 _90144 x t x').
Proof. exact (TRANS (@lem3473509 _90144 x x' t) (@lem3473524 _90144 x t x')). Qed.
Lemma lem3473528 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term34 _90144 s x' x t) = (term100 _90144 s x t x').
Proof. exact (MK_COMB (@lem3473505 _90144 s x) (@lem3473527 _90144 x t x')). Qed.
Lemma lem3473531 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term36 _90144 s x t) = (term101 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3473528 _90144 s x' t x)). Qed.
Lemma lem3473532 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473533 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term38 _90144 s x t) = (term102 _90144 s t x).
Proof. exact (MK_COMB (@lem3473532 _90144) (@lem3473531 _90144 s t x)). Qed.
Lemma lem3473538 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term94 _90144 x s t) = (term102 _90144 s t x).
Proof. exact (TRANS (@lem3473493 _90144 s x t) (@lem3473533 _90144 s t x)). Qed.
Lemma lem3473539 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term67 _90144 x s t) = (term94 _90144 x s t)) = ((term81 _90144 s t x) = (term102 _90144 s t x)).
Proof. exact (MK_COMB (@lem3473471 _90144 s t x) (@lem3473538 _90144 s t x)). Qed.
Lemma lem3473542 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term103 _90144 s t) = (term104 _90144 s t).
Proof. exact (fun_ext (fun x : _90144 => @lem3473539 _90144 s t x)). Qed.
Lemma lem3473543 {_90144 : Type'} : (@all _90144) = (@all _90144).
Proof. exact (eq_refl (@all _90144)). Qed.
Lemma lem3473544 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term61 _90144 s t) = (term105 _90144 s t).
Proof. exact (MK_COMB (@lem3473543 _90144) (@lem3473542 _90144 s t)). Qed.
Lemma lem3473549 {_90144 : Type'} (s : type686 _90144) : (term62 _90144 s) = (term106 _90144 s).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473544 _90144 s t)). Qed.
Lemma lem3473550 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3473551 {_90144 : Type'} (s : type686 _90144) : (term63 _90144 s) = (term107 _90144 s).
Proof. exact (MK_COMB (@lem3473550 _90144) (@lem3473549 _90144 s)). Qed.
Lemma lem3473556 {_90144 : Type'} : (term64 _90144) = (term108 _90144).
Proof. exact (fun_ext (fun s : type686 _90144 => @lem3473551 _90144 s)). Qed.
Lemma lem3473557 {_90144 : Type'} : (@all ((_90144 -> Prop) -> Prop)) = (@all ((_90144 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90144 -> Prop) -> Prop))). Qed.
Lemma lem3473558 {_90144 : Type'} : (term65 _90144) = (term109 _90144).
Proof. exact (MK_COMB (@lem3473557 _90144) (@lem3473556 _90144)). Qed.
Lemma lem3473563 {_90144 : Type'} : (term109 _90144) = (term65 _90144).
Proof. exact (SYM (@lem3473558 _90144)). Qed.
Lemma lem3473565 (p : Prop) : p = (term110 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3473566 {_90144 : Type'} : (term109 _90144) = (term111 _90144).
Proof. exact (@lem3473565 (term109 _90144)). Qed.
Lemma lem3473567 {_90144 : Type'} : (term111 _90144) = (term109 _90144).
Proof. exact (SYM (@lem3473566 _90144)). Qed.
Lemma lem3473568 {_90144 : Type'} (h1 : term112 _90144) : term112 _90144.
Proof. exact (h1). Qed.
Lemma lem3473571 {_90144 : Type'} (h1 : term111 _90144) : term111 _90144.
Proof. exact (h1). Qed.
Lemma lem3473572 {_90144 : Type'} : term113 _90144.
Proof. exact (fun h0 : term111 _90144 => @lem3473571 _90144 h0). Qed.
Lemma lem3473573 {_90144 : Type'} (h1 : term113 _90144) : term113 _90144.
Proof. exact (h1). Qed.
Lemma lem3473574 {_90144 : Type'} (h1 : term111 _90144) : term111 _90144.
Proof. exact (h1). Qed.
Lemma lem3473575 {_90144 : Type'} (h1 : term111 _90144) (h2 : term113 _90144) : term111 _90144.
Proof. exact (@lem3473573 _90144 h2 (@lem3473574 _90144 h1)). Qed.
Lemma lem3473576 {_90144 : Type'} (h1 : term111 _90144) : term114 _90144.
Proof. exact (fun h0 : term113 _90144 => @lem3473575 _90144 h1 h0). Qed.
Lemma lem3473577 {_90144 : Type'} (h1 : term113 _90144) : term113 _90144.
Proof. exact (h1). Qed.
Lemma lem3473578 {_90144 : Type'} (h1 : term111 _90144) (h2 : term113 _90144) : term111 _90144.
Proof. exact (@lem3473576 _90144 h1 (@lem3473577 _90144 h2)). Qed.
Lemma lem3473579 {_90144 : Type'} (h1 : term113 _90144) : term113 _90144.
Proof. exact (fun h0 : term111 _90144 => @lem3473578 _90144 h0 h1). Qed.
Lemma lem3473580 {_90144 : Type'} : term115 _90144.
Proof. exact (fun h0 : term113 _90144 => @lem3473579 _90144 h0). Qed.
Lemma lem3473583 {_90144 : Type'} : term113 _90144.
Proof. exact (@lem3473580 _90144 (@lem3473572 _90144)). Qed.
Lemma lem3473584 {_90144 : Type'} : term113 _90144.
Proof. exact (@lem3473583 _90144). Qed.
Lemma lem3473586 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3473587 {_90144 : Type'} : (term111 _90144) = (term116 _90144).
Proof. exact (@lem3473586 (term112 _90144)). Qed.
Lemma lem3473589 (t : Prop) : (term117 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3473590 {_90144 : Type'} : (term116 _90144) = (term109 _90144).
Proof. exact (@lem3473589 (term109 _90144)). Qed.
Lemma lem3473671 {_90144 : Type'} : (term111 _90144) = (term109 _90144).
Proof. exact (TRANS (@lem3473587 _90144) (@lem3473590 _90144)). Qed.
Lemma lem3473682 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term100 _90144 s x t x') = (term100 _90144 s x t x').
Proof. exact (eq_refl (term100 _90144 s x t x')). Qed.
Lemma lem3473683 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term101 _90144 s t x) = (term101 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3473682 _90144 s x' t x)). Qed.
Lemma lem3473684 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473685 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term102 _90144 s t x) = (term102 _90144 s t x).
Proof. exact (MK_COMB (@lem3473684 _90144) (@lem3473683 _90144 s t x)). Qed.
Lemma lem3473688 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term80 _90144 t x) = (term80 _90144 t x).
Proof. exact (eq_refl (term80 _90144 t x)). Qed.
Lemma lem3473693 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term73 _90144 s t x) = (term73 _90144 s t x).
Proof. exact (eq_refl (term73 _90144 s t x)). Qed.
Lemma lem3473694 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term75 _90144 s x) = (term75 _90144 s x).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473693 _90144 s t x)). Qed.
Lemma lem3473695 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473696 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term76 _90144 s x) = (term76 _90144 s x).
Proof. exact (MK_COMB (@lem3473695 _90144) (@lem3473694 _90144 s x)). Qed.
Lemma lem3473697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473698 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term78 _90144 s x) = (term78 _90144 s x).
Proof. exact (MK_COMB (@lem3473697) (@lem3473696 _90144 s x)). Qed.
Lemma lem3473699 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term81 _90144 s t x) = (term81 _90144 s t x).
Proof. exact (MK_COMB (@lem3473698 _90144 s x) (@lem3473688 _90144 t x)). Qed.
Lemma lem3473700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3473701 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term83 _90144 s t x) = (term83 _90144 s t x).
Proof. exact (MK_COMB (@lem3473700) (@lem3473699 _90144 s t x)). Qed.
Lemma lem3473702 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term81 _90144 s t x) = (term102 _90144 s t x)) = ((term81 _90144 s t x) = (term102 _90144 s t x)).
Proof. exact (MK_COMB (@lem3473701 _90144 s t x) (@lem3473685 _90144 s t x)). Qed.
Lemma lem3473703 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term104 _90144 s t) = (term104 _90144 s t).
Proof. exact (fun_ext (fun x : _90144 => @lem3473702 _90144 s t x)). Qed.
Lemma lem3473704 {_90144 : Type'} : (@all _90144) = (@all _90144).
Proof. exact (eq_refl (@all _90144)). Qed.
Lemma lem3473705 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term105 _90144 s t) = (term105 _90144 s t).
Proof. exact (MK_COMB (@lem3473704 _90144) (@lem3473703 _90144 s t)). Qed.
Lemma lem3473706 {_90144 : Type'} (s : type686 _90144) : (term106 _90144 s) = (term106 _90144 s).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473705 _90144 s t)). Qed.
Lemma lem3473707 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3473708 {_90144 : Type'} (s : type686 _90144) : (term107 _90144 s) = (term107 _90144 s).
Proof. exact (MK_COMB (@lem3473707 _90144) (@lem3473706 _90144 s)). Qed.
Lemma lem3473709 {_90144 : Type'} : (term108 _90144) = (term108 _90144).
Proof. exact (fun_ext (fun s : type686 _90144 => @lem3473708 _90144 s)). Qed.
Lemma lem3473710 {_90144 : Type'} : (@all ((_90144 -> Prop) -> Prop)) = (@all ((_90144 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90144 -> Prop) -> Prop))). Qed.
Lemma lem3473711 {_90144 : Type'} : (term109 _90144) = (term109 _90144).
Proof. exact (MK_COMB (@lem3473710 _90144) (@lem3473709 _90144)). Qed.
Lemma lem3473752 {_90144 : Type'} : (term111 _90144) = (term109 _90144).
Proof. exact (TRANS (@lem3473671 _90144) (@lem3473711 _90144)). Qed.
Lemma lem3473753 {_90144 : Type'} : (term109 _90144) = (term111 _90144).
Proof. exact (SYM (@lem3473752 _90144)). Qed.
Lemma lem3473755 (p : Prop) : p = (term110 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3473756 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term81 _90144 s t x) = (term102 _90144 s t x)) = (term118 _90144 s t x).
Proof. exact (@lem3473755 ((term81 _90144 s t x) = (term102 _90144 s t x))). Qed.
Lemma lem3473757 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term118 _90144 s t x) = ((term81 _90144 s t x) = (term102 _90144 s t x)).
Proof. exact (SYM (@lem3473756 _90144 s t x)). Qed.
Lemma lem3473758 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term119 _90144 s t x) : term119 _90144 s t x.
Proof. exact (h1). Qed.
Lemma lem3473767 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term120 _90144 s t x) = (term121 _90144 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3473770 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term73 _90144 s t x) = (term73 _90144 s t x).
Proof. exact (eq_refl (term73 _90144 s t x)). Qed.
Lemma lem3473771 {_90144 : Type'} (P : type686 _90144) : (term122 _90144 P) = (term123 _90144 P).
Proof. exact (@lem18394 (_90144 -> Prop) P). Qed.
Lemma lem3473772 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term124 _90144 s x) = (term125 _90144 s x).
Proof. exact (@lem3473771 _90144 (term75 _90144 s x)). Qed.
Lemma lem3473773 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term126 _90144 s x t) = (term73 _90144 s t x).
Proof. exact (eq_refl (term126 _90144 s x t)). Qed.
Lemma lem3473774 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3473775 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term127 _90144 s x t) = (term120 _90144 s t x).
Proof. exact (MK_COMB (@lem3473774) (@lem3473773 _90144 s t x)). Qed.
Lemma lem3473776 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term127 _90144 s x t) = (term121 _90144 s t x).
Proof. exact (TRANS (@lem3473775 _90144 s t x) (@lem3473767 _90144 s t x)). Qed.
Lemma lem3473777 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term128 _90144 s x) = (term129 _90144 s x).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473776 _90144 s t x)). Qed.
Lemma lem3473778 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3473779 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term125 _90144 s x) = (term130 _90144 s x).
Proof. exact (MK_COMB (@lem3473778 _90144) (@lem3473777 _90144 s x)). Qed.
Lemma lem3473780 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term124 _90144 s x) = (term130 _90144 s x).
Proof. exact (TRANS (@lem3473772 _90144 s x) (@lem3473779 _90144 s x)). Qed.
Lemma lem3473781 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term75 _90144 s x) = (term75 _90144 s x).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3473770 _90144 s t x)). Qed.
Lemma lem3473782 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473783 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term76 _90144 s x) = (term76 _90144 s x).
Proof. exact (MK_COMB (@lem3473782 _90144) (@lem3473781 _90144 s x)). Qed.
Lemma lem3473784 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term80 _90144 t x) = (term80 _90144 t x).
Proof. exact (eq_refl (term80 _90144 t x)). Qed.
Lemma lem3473787 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term131 _90144 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3473788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3473789 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term132 _90144 s x) = (term133 _90144 s x).
Proof. exact (MK_COMB (@lem3473788) (@lem3473780 _90144 s x)). Qed.
Lemma lem3473790 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term134 _90144 s t x) = (term135 _90144 s t x).
Proof. exact (MK_COMB (@lem3473789 _90144 s x) (@lem3473787 _90144 t x)). Qed.
Lemma lem3473791 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term136 _90144 s t x) = (term134 _90144 s t x).
Proof. exact (@lem17045 (term76 _90144 s x) (term80 _90144 t x)). Qed.
Lemma lem3473792 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term136 _90144 s t x) = (term135 _90144 s t x).
Proof. exact (TRANS (@lem3473791 _90144 s t x) (@lem3473790 _90144 s t x)). Qed.
Lemma lem3473793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473794 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term78 _90144 s x) = (term78 _90144 s x).
Proof. exact (MK_COMB (@lem3473793) (@lem3473783 _90144 s x)). Qed.
Lemma lem3473795 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term81 _90144 s t x) = (term81 _90144 s t x).
Proof. exact (MK_COMB (@lem3473794 _90144 s x) (@lem3473784 _90144 t x)). Qed.
Lemma lem3473803 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term131 _90144 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3473805 {_90144 : Type'} (x : _90144 -> Prop) (x' : _90144) : (term137 _90144 x x') = (term137 _90144 x x').
Proof. exact (eq_refl (term137 _90144 x x')). Qed.
Lemma lem3473806 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term138 _90144 x t x') = (term139 _90144 x t x').
Proof. exact (MK_COMB (@lem3473805 _90144 x x') (@lem3473803 _90144 t x')). Qed.
Lemma lem3473807 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term140 _90144 x t x') = (term138 _90144 x t x').
Proof. exact (@lem17045 (x x') (term80 _90144 t x')). Qed.
Lemma lem3473808 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term140 _90144 x t x') = (term139 _90144 x t x').
Proof. exact (TRANS (@lem3473807 _90144 x t x') (@lem3473806 _90144 x t x')). Qed.
Lemma lem3473813 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) : (term141 _90144 s x) = (term141 _90144 s x).
Proof. exact (eq_refl (term141 _90144 s x)). Qed.
Lemma lem3473814 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term142 _90144 s x t x') = (term143 _90144 s x t x').
Proof. exact (MK_COMB (@lem3473813 _90144 s x) (@lem3473808 _90144 x t x')). Qed.
Lemma lem3473815 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term144 _90144 s x t x') = (term142 _90144 s x t x').
Proof. exact (@lem17045 (s x) (term99 _90144 x t x')). Qed.
Lemma lem3473816 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term144 _90144 s x t x') = (term143 _90144 s x t x').
Proof. exact (TRANS (@lem3473815 _90144 s x t x') (@lem3473814 _90144 s x t x')). Qed.
Lemma lem3473819 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term100 _90144 s x t x') = (term100 _90144 s x t x').
Proof. exact (eq_refl (term100 _90144 s x t x')). Qed.
Lemma lem3473820 {_90144 : Type'} (P : type686 _90144) : (term122 _90144 P) = (term123 _90144 P).
Proof. exact (@lem18394 (_90144 -> Prop) P). Qed.
Lemma lem3473821 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term145 _90144 s t x) = (term146 _90144 s t x).
Proof. exact (@lem3473820 _90144 (term101 _90144 s t x)). Qed.
Lemma lem3473822 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term147 _90144 s t x' x) = (term100 _90144 s x t x').
Proof. exact (eq_refl (term147 _90144 s t x' x)). Qed.
Lemma lem3473823 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3473824 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term148 _90144 s t x' x) = (term144 _90144 s x t x').
Proof. exact (MK_COMB (@lem3473823) (@lem3473822 _90144 s x t x')). Qed.
Lemma lem3473825 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term148 _90144 s t x' x) = (term143 _90144 s x t x').
Proof. exact (TRANS (@lem3473824 _90144 s x t x') (@lem3473816 _90144 s x t x')). Qed.
Lemma lem3473826 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term149 _90144 s t x) = (term150 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3473825 _90144 s x' t x)). Qed.
Lemma lem3473827 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3473828 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term146 _90144 s t x) = (term151 _90144 s t x).
Proof. exact (MK_COMB (@lem3473827 _90144) (@lem3473826 _90144 s t x)). Qed.
Lemma lem3473829 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term145 _90144 s t x) = (term151 _90144 s t x).
Proof. exact (TRANS (@lem3473821 _90144 s t x) (@lem3473828 _90144 s t x)). Qed.
Lemma lem3473830 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term101 _90144 s t x) = (term101 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3473819 _90144 s x' t x)). Qed.
Lemma lem3473831 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3473832 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term102 _90144 s t x) = (term102 _90144 s t x).
Proof. exact (MK_COMB (@lem3473831 _90144) (@lem3473830 _90144 s t x)). Qed.
Lemma lem3473833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473834 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term152 _90144 s t x) = (term153 _90144 s t x).
Proof. exact (MK_COMB (@lem3473833) (@lem3473792 _90144 s t x)). Qed.
Lemma lem3473835 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term154 _90144 s t x) = (term155 _90144 s t x).
Proof. exact (MK_COMB (@lem3473834 _90144 s t x) (@lem3473832 _90144 s t x)). Qed.
Lemma lem3473836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473837 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term156 _90144 s t x) = (term156 _90144 s t x).
Proof. exact (MK_COMB (@lem3473836) (@lem3473795 _90144 s t x)). Qed.
Lemma lem3473838 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term157 _90144 s t x) = (term158 _90144 s t x).
Proof. exact (MK_COMB (@lem3473837 _90144 s t x) (@lem3473829 _90144 s t x)). Qed.
Lemma lem3473839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3473840 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term159 _90144 s t x) = (term160 _90144 s t x).
Proof. exact (MK_COMB (@lem3473839) (@lem3473838 _90144 s t x)). Qed.
Lemma lem3473841 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term161 _90144 s t x) = (term162 _90144 s t x).
Proof. exact (MK_COMB (@lem3473840 _90144 s t x) (@lem3473835 _90144 s t x)). Qed.
Lemma lem3473842 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term119 _90144 s t x) = (term161 _90144 s t x).
Proof. exact (@lem17646 (term81 _90144 s t x) (term102 _90144 s t x)). Qed.
Lemma lem3473843 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term119 _90144 s t x) = (term162 _90144 s t x).
Proof. exact (TRANS (@lem3473842 _90144 s t x) (@lem3473841 _90144 s t x)). Qed.
Lemma lem3473998 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3473999 {_90144 : Type'} (P : type686 _90144) (Q : Prop) : (term165 _90144 P Q) = (term166 _90144 P Q).
Proof. exact (@lem3473998 (_90144 -> Prop) P Q). Qed.
Lemma lem3474000 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term167 _90144 s t x) = (term168 _90144 s t x).
Proof. exact (@lem3473999 _90144 (term75 _90144 s x) (term80 _90144 t x)). Qed.
Lemma lem3474001 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term126 _90144 s x t) = (term73 _90144 s t x).
Proof. exact (eq_refl (term126 _90144 s x t)). Qed.
Lemma lem3474002 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term169 _90144 s x) = (term75 _90144 s x).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3474001 _90144 s t x)). Qed.
Lemma lem3474003 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474004 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term170 _90144 s x) = (term76 _90144 s x).
Proof. exact (MK_COMB (@lem3474003 _90144) (@lem3474002 _90144 s x)). Qed.
Lemma lem3474005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474006 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term171 _90144 s x) = (term78 _90144 s x).
Proof. exact (MK_COMB (@lem3474005) (@lem3474004 _90144 s x)). Qed.
Lemma lem3474007 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term80 _90144 t x) = (term80 _90144 t x).
Proof. exact (eq_refl (term80 _90144 t x)). Qed.
Lemma lem3474008 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term167 _90144 s t x) = (term81 _90144 s t x).
Proof. exact (MK_COMB (@lem3474006 _90144 s x) (@lem3474007 _90144 t x)). Qed.
Lemma lem3474009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474010 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term172 _90144 s t x) = (term83 _90144 s t x).
Proof. exact (MK_COMB (@lem3474009) (@lem3474008 _90144 s t x)). Qed.
Lemma lem3474011 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (x : _90144) : (term126 _90144 s x t') = (term73 _90144 s t' x).
Proof. exact (eq_refl (term126 _90144 s x t')). Qed.
Lemma lem3474012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474013 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (x : _90144) : (term173 _90144 s x t') = (term174 _90144 s t' x).
Proof. exact (MK_COMB (@lem3474012) (@lem3474011 _90144 s t' x)). Qed.
Lemma lem3474014 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term80 _90144 t x) = (term80 _90144 t x).
Proof. exact (eq_refl (term80 _90144 t x)). Qed.
Lemma lem3474015 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term175 _90144 s t' t x) = (term176 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474013 _90144 s t' x) (@lem3474014 _90144 t x)). Qed.
Lemma lem3474016 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term177 _90144 s t x) = (term178 _90144 s t x).
Proof. exact (fun_ext (fun t' : _90144 -> Prop => @lem3474015 _90144 s t' t x)). Qed.
Lemma lem3474017 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474018 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term168 _90144 s t x) = (term179 _90144 s t x).
Proof. exact (MK_COMB (@lem3474017 _90144) (@lem3474016 _90144 s t x)). Qed.
Lemma lem3474019 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term167 _90144 s t x) = (term168 _90144 s t x)) = ((term81 _90144 s t x) = (term179 _90144 s t x)).
Proof. exact (MK_COMB (@lem3474010 _90144 s t x) (@lem3474018 _90144 s t x)). Qed.
Lemma lem3474020 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term81 _90144 s t x) = (term179 _90144 s t x).
Proof. exact (EQ_MP (@lem3474019 _90144 s t x) (@lem3474000 _90144 s t x)). Qed.
Lemma lem3474021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474022 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term156 _90144 s t x) = (term180 _90144 s t x).
Proof. exact (MK_COMB (@lem3474021) (@lem3474020 _90144 s t x)). Qed.
Lemma lem3474023 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term151 _90144 s t x) = (term151 _90144 s t x).
Proof. exact (eq_refl (term151 _90144 s t x)). Qed.
Lemma lem3474024 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term158 _90144 s t x) = (term181 _90144 s t x).
Proof. exact (MK_COMB (@lem3474022 _90144 s t x) (@lem3474023 _90144 s t x)). Qed.
Lemma lem3474026 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3474027 {_90144 : Type'} (P : type686 _90144) (Q : Prop) : (term165 _90144 P Q) = (term166 _90144 P Q).
Proof. exact (@lem3474026 (_90144 -> Prop) P Q). Qed.
Lemma lem3474028 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term182 _90144 s t x) = (term183 _90144 s t x).
Proof. exact (@lem3474027 _90144 (term178 _90144 s t x) (term151 _90144 s t x)). Qed.
Lemma lem3474029 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term184 _90144 s t x t') = (term176 _90144 s t' t x).
Proof. exact (eq_refl (term184 _90144 s t x t')). Qed.
Lemma lem3474030 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term185 _90144 s t x) = (term178 _90144 s t x).
Proof. exact (fun_ext (fun t' : _90144 -> Prop => @lem3474029 _90144 s t' t x)). Qed.
Lemma lem3474031 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474032 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term186 _90144 s t x) = (term179 _90144 s t x).
Proof. exact (MK_COMB (@lem3474031 _90144) (@lem3474030 _90144 s t x)). Qed.
Lemma lem3474033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474034 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term187 _90144 s t x) = (term180 _90144 s t x).
Proof. exact (MK_COMB (@lem3474033) (@lem3474032 _90144 s t x)). Qed.
Lemma lem3474035 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term151 _90144 s t x) = (term151 _90144 s t x).
Proof. exact (eq_refl (term151 _90144 s t x)). Qed.
Lemma lem3474036 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term182 _90144 s t x) = (term181 _90144 s t x).
Proof. exact (MK_COMB (@lem3474034 _90144 s t x) (@lem3474035 _90144 s t x)). Qed.
Lemma lem3474037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474038 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term188 _90144 s t x) = (term189 _90144 s t x).
Proof. exact (MK_COMB (@lem3474037) (@lem3474036 _90144 s t x)). Qed.
Lemma lem3474039 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term184 _90144 s t x t') = (term176 _90144 s t' t x).
Proof. exact (eq_refl (term184 _90144 s t x t')). Qed.
Lemma lem3474040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474041 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term190 _90144 s t x t') = (term191 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474040) (@lem3474039 _90144 s t' t x)). Qed.
Lemma lem3474042 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term151 _90144 s t x) = (term151 _90144 s t x).
Proof. exact (eq_refl (term151 _90144 s t x)). Qed.
Lemma lem3474043 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term192 _90144 t' s t x) = (term193 _90144 t' s t x).
Proof. exact (MK_COMB (@lem3474041 _90144 s t' t x) (@lem3474042 _90144 s t x)). Qed.
Lemma lem3474044 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term194 _90144 s t x) = (term195 _90144 s t x).
Proof. exact (fun_ext (fun t' : _90144 -> Prop => @lem3474043 _90144 t' s t x)). Qed.
Lemma lem3474045 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474046 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term183 _90144 s t x) = (term196 _90144 s t x).
Proof. exact (MK_COMB (@lem3474045 _90144) (@lem3474044 _90144 s t x)). Qed.
Lemma lem3474047 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term182 _90144 s t x) = (term183 _90144 s t x)) = ((term181 _90144 s t x) = (term196 _90144 s t x)).
Proof. exact (MK_COMB (@lem3474038 _90144 s t x) (@lem3474046 _90144 s t x)). Qed.
Lemma lem3474048 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term181 _90144 s t x) = (term196 _90144 s t x).
Proof. exact (EQ_MP (@lem3474047 _90144 s t x) (@lem3474028 _90144 s t x)). Qed.
Lemma lem3474049 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term158 _90144 s t x) = (term196 _90144 s t x).
Proof. exact (TRANS (@lem3474024 _90144 s t x) (@lem3474048 _90144 s t x)). Qed.
Lemma lem3474050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474051 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term160 _90144 s t x) = (term197 _90144 s t x).
Proof. exact (MK_COMB (@lem3474050) (@lem3474049 _90144 s t x)). Qed.
Lemma lem3474053 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3474054 {_90144 : Type'} (P : Prop) (Q : type686 _90144) : (term200 _90144 P Q) = (term201 _90144 P Q).
Proof. exact (@lem3474053 (_90144 -> Prop) P Q). Qed.
Lemma lem3474055 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term202 _90144 s t x) = (term203 _90144 s t x).
Proof. exact (@lem3474054 _90144 (term135 _90144 s t x) (term101 _90144 s t x)). Qed.
Lemma lem3474056 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term147 _90144 s t x' x) = (term100 _90144 s x t x').
Proof. exact (eq_refl (term147 _90144 s t x' x)). Qed.
Lemma lem3474057 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term204 _90144 s t x) = (term101 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3474056 _90144 s x' t x)). Qed.
Lemma lem3474058 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474059 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term205 _90144 s t x) = (term102 _90144 s t x).
Proof. exact (MK_COMB (@lem3474058 _90144) (@lem3474057 _90144 s t x)). Qed.
Lemma lem3474060 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term153 _90144 s t x) = (term153 _90144 s t x).
Proof. exact (eq_refl (term153 _90144 s t x)). Qed.
Lemma lem3474061 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term202 _90144 s t x) = (term155 _90144 s t x).
Proof. exact (MK_COMB (@lem3474060 _90144 s t x) (@lem3474059 _90144 s t x)). Qed.
Lemma lem3474062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474063 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term206 _90144 s t x) = (term207 _90144 s t x).
Proof. exact (MK_COMB (@lem3474062) (@lem3474061 _90144 s t x)). Qed.
Lemma lem3474064 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term147 _90144 s t x' x) = (term100 _90144 s x t x').
Proof. exact (eq_refl (term147 _90144 s t x' x)). Qed.
Lemma lem3474065 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term153 _90144 s t x) = (term153 _90144 s t x).
Proof. exact (eq_refl (term153 _90144 s t x)). Qed.
Lemma lem3474066 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term208 _90144 s t x' x) = (term209 _90144 s x t x').
Proof. exact (MK_COMB (@lem3474065 _90144 s t x') (@lem3474064 _90144 s x t x')). Qed.
Lemma lem3474067 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term210 _90144 s t x) = (term211 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3474066 _90144 s x' t x)). Qed.
Lemma lem3474068 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474069 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term203 _90144 s t x) = (term212 _90144 s t x).
Proof. exact (MK_COMB (@lem3474068 _90144) (@lem3474067 _90144 s t x)). Qed.
Lemma lem3474070 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term202 _90144 s t x) = (term203 _90144 s t x)) = ((term155 _90144 s t x) = (term212 _90144 s t x)).
Proof. exact (MK_COMB (@lem3474063 _90144 s t x) (@lem3474069 _90144 s t x)). Qed.
Lemma lem3474071 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term155 _90144 s t x) = (term212 _90144 s t x).
Proof. exact (EQ_MP (@lem3474070 _90144 s t x) (@lem3474055 _90144 s t x)). Qed.
Lemma lem3474072 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term162 _90144 s t x) = (term213 _90144 s t x).
Proof. exact (MK_COMB (@lem3474051 _90144 s t x) (@lem3474071 _90144 s t x)). Qed.
Lemma lem3474074 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term214 A P Q) = (term215 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3474075 {_90144 : Type'} (P : type686 _90144) (Q : type686 _90144) : (term216 _90144 P Q) = (term217 _90144 P Q).
Proof. exact (@lem3474074 (_90144 -> Prop) P Q). Qed.
Lemma lem3474076 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term218 _90144 s t x) = (term219 _90144 s t x).
Proof. exact (@lem3474075 _90144 (term195 _90144 s t x) (term211 _90144 s t x)). Qed.
Lemma lem3474077 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term220 _90144 s t x t') = (term193 _90144 t' s t x).
Proof. exact (eq_refl (term220 _90144 s t x t')). Qed.
Lemma lem3474078 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term221 _90144 s t x) = (term195 _90144 s t x).
Proof. exact (fun_ext (fun t' : _90144 -> Prop => @lem3474077 _90144 t' s t x)). Qed.
Lemma lem3474079 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474080 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term222 _90144 s t x) = (term196 _90144 s t x).
Proof. exact (MK_COMB (@lem3474079 _90144) (@lem3474078 _90144 s t x)). Qed.
Lemma lem3474081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474082 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term223 _90144 s t x) = (term197 _90144 s t x).
Proof. exact (MK_COMB (@lem3474081) (@lem3474080 _90144 s t x)). Qed.
Lemma lem3474083 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term224 _90144 s t x t') = (term209 _90144 s t' t x).
Proof. exact (eq_refl (term224 _90144 s t x t')). Qed.
Lemma lem3474084 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term225 _90144 s t x) = (term211 _90144 s t x).
Proof. exact (fun_ext (fun t' : _90144 -> Prop => @lem3474083 _90144 s t' t x)). Qed.
Lemma lem3474085 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474086 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term226 _90144 s t x) = (term212 _90144 s t x).
Proof. exact (MK_COMB (@lem3474085 _90144) (@lem3474084 _90144 s t x)). Qed.
Lemma lem3474087 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term218 _90144 s t x) = (term213 _90144 s t x).
Proof. exact (MK_COMB (@lem3474082 _90144 s t x) (@lem3474086 _90144 s t x)). Qed.
Lemma lem3474088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474089 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term227 _90144 s t x) = (term228 _90144 s t x).
Proof. exact (MK_COMB (@lem3474088) (@lem3474087 _90144 s t x)). Qed.
Lemma lem3474090 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term220 _90144 s t x t') = (term193 _90144 t' s t x).
Proof. exact (eq_refl (term220 _90144 s t x t')). Qed.
Lemma lem3474091 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474092 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term229 _90144 s t x t') = (term230 _90144 t' s t x).
Proof. exact (MK_COMB (@lem3474091) (@lem3474090 _90144 t' s t x)). Qed.
Lemma lem3474093 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term224 _90144 s t x t') = (term209 _90144 s t' t x).
Proof. exact (eq_refl (term224 _90144 s t x t')). Qed.
Lemma lem3474094 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term231 _90144 s t x t') = (term232 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474092 _90144 t' s t x) (@lem3474093 _90144 s t' t x)). Qed.
Lemma lem3474095 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term233 _90144 s t x) = (term234 _90144 s t x).
Proof. exact (fun_ext (fun t' : _90144 -> Prop => @lem3474094 _90144 s t' t x)). Qed.
Lemma lem3474096 {_90144 : Type'} : (@ex (_90144 -> Prop)) = (@ex (_90144 -> Prop)).
Proof. exact (eq_refl (@ex (_90144 -> Prop))). Qed.
Lemma lem3474097 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term219 _90144 s t x) = (term235 _90144 s t x).
Proof. exact (MK_COMB (@lem3474096 _90144) (@lem3474095 _90144 s t x)). Qed.
Lemma lem3474098 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term218 _90144 s t x) = (term219 _90144 s t x)) = ((term213 _90144 s t x) = (term235 _90144 s t x)).
Proof. exact (MK_COMB (@lem3474089 _90144 s t x) (@lem3474097 _90144 s t x)). Qed.
Lemma lem3474099 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term213 _90144 s t x) = (term235 _90144 s t x).
Proof. exact (EQ_MP (@lem3474098 _90144 s t x) (@lem3474076 _90144 s t x)). Qed.
Lemma lem3474102 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term236 _90144 s t x) = (term236 _90144 s t x).
Proof. exact (eq_refl (term236 _90144 s t x)). Qed.
Lemma lem3474103 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term236 _90144 s t x) = ((term213 _90144 s t x) = (term235 _90144 s t x)).
Proof. exact (eq_refl (term236 _90144 s t x)). Qed.
Lemma lem3474104 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term237 _90144 s t x) = (term237 _90144 s t x).
Proof. exact (eq_refl (term237 _90144 s t x)). Qed.
Lemma lem3474105 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term236 _90144 s t x) = (term236 _90144 s t x)) = ((term236 _90144 s t x) = ((term213 _90144 s t x) = (term235 _90144 s t x))).
Proof. exact (MK_COMB (@lem3474104 _90144 s t x) (@lem3474103 _90144 s t x)). Qed.
Lemma lem3474106 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term236 _90144 s t x) = ((term213 _90144 s t x) = (term235 _90144 s t x)).
Proof. exact (eq_refl (term236 _90144 s t x)). Qed.
Lemma lem3474107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474108 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term237 _90144 s t x) = (term238 _90144 s t x).
Proof. exact (MK_COMB (@lem3474107) (@lem3474106 _90144 s t x)). Qed.
Lemma lem3474109 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term213 _90144 s t x) = (term235 _90144 s t x)) = ((term213 _90144 s t x) = (term235 _90144 s t x)).
Proof. exact (eq_refl ((term213 _90144 s t x) = (term235 _90144 s t x))). Qed.
Lemma lem3474110 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term236 _90144 s t x) = ((term213 _90144 s t x) = (term235 _90144 s t x))) = (((term213 _90144 s t x) = (term235 _90144 s t x)) = ((term213 _90144 s t x) = (term235 _90144 s t x))).
Proof. exact (MK_COMB (@lem3474108 _90144 s t x) (@lem3474109 _90144 s t x)). Qed.
Lemma lem3474111 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term236 _90144 s t x) = (term236 _90144 s t x)) = (((term213 _90144 s t x) = (term235 _90144 s t x)) = ((term213 _90144 s t x) = (term235 _90144 s t x))).
Proof. exact (TRANS (@lem3474105 _90144 s t x) (@lem3474110 _90144 s t x)). Qed.
Lemma lem3474112 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : ((term213 _90144 s t x) = (term235 _90144 s t x)) = ((term213 _90144 s t x) = (term235 _90144 s t x)).
Proof. exact (EQ_MP (@lem3474111 _90144 s t x) (@lem3474102 _90144 s t x)). Qed.
Lemma lem3474113 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term213 _90144 s t x) = (term235 _90144 s t x).
Proof. exact (EQ_MP (@lem3474112 _90144 s t x) (@lem3474099 _90144 s t x)). Qed.
Lemma lem3474115 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term162 _90144 s t x) = (term235 _90144 s t x).
Proof. exact (TRANS (@lem3474072 _90144 s t x) (@lem3474113 _90144 s t x)). Qed.
Lemma lem3474116 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term119 _90144 s t x) = (term235 _90144 s t x).
Proof. exact (TRANS (@lem3473843 _90144 s t x) (@lem3474115 _90144 s t x)). Qed.
Lemma lem3474117 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term119 _90144 s t x) : term235 _90144 s t x.
Proof. exact (EQ_MP (@lem3474116 _90144 s t x) (@lem3473758 _90144 s t x h1)). Qed.
Lemma lem3474118 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term232 _90144 s t' t x) : term232 _90144 s t' t x.
Proof. exact (h1). Qed.
Lemma lem3474119 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474124 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474125 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474124 _90144 Prop f x). Qed.
Lemma lem3474127 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (t x) = (@I (_90144 -> Prop) t x).
Proof. exact (@lem3474125 _90144 t x). Qed.
Lemma lem3474128 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term80 _90144 t x) = (term239 _90144 t x).
Proof. exact (MK_COMB (@lem3474119) (@lem3474127 _90144 t x)). Qed.
Lemma lem3474133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474134 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474133 _90144 Prop f x). Qed.
Lemma lem3474136 {_90144 : Type'} (t' : _90144 -> Prop) (x : _90144) : (t' x) = (@I (_90144 -> Prop) t' x).
Proof. exact (@lem3474134 _90144 t' x). Qed.
Lemma lem3474137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474138 {_90144 : Type'} (t' : _90144 -> Prop) (x : _90144) : (term98 _90144 t' x) = (term240 _90144 t' x).
Proof. exact (MK_COMB (@lem3474137) (@lem3474136 _90144 t' x)). Qed.
Lemma lem3474139 {_90144 : Type'} (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term99 _90144 t' t x) = (term241 _90144 t' t x).
Proof. exact (MK_COMB (@lem3474138 _90144 t' x) (@lem3474128 _90144 t x)). Qed.
Lemma lem3474144 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474145 {_90144 : Type'} (f : type686 _90144) (x : _90144 -> Prop) : (f x) = (@I ((_90144 -> Prop) -> Prop) f x).
Proof. exact (@lem3474144 (_90144 -> Prop) Prop f x). Qed.
Lemma lem3474147 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) : (s t') = (@I ((_90144 -> Prop) -> Prop) s t').
Proof. exact (@lem3474145 _90144 s t'). Qed.
Lemma lem3474148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474149 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) : (term71 _90144 s t') = (term242 _90144 s t').
Proof. exact (MK_COMB (@lem3474148) (@lem3474147 _90144 s t')). Qed.
Lemma lem3474150 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term100 _90144 s t' t x) = (term243 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474149 _90144 s t') (@lem3474139 _90144 t' t x)). Qed.
Lemma lem3474155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474156 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474155 _90144 Prop f x). Qed.
Lemma lem3474158 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (t x) = (@I (_90144 -> Prop) t x).
Proof. exact (@lem3474156 _90144 t x). Qed.
Lemma lem3474159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474164 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474165 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474164 _90144 Prop f x). Qed.
Lemma lem3474167 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (t x) = (@I (_90144 -> Prop) t x).
Proof. exact (@lem3474165 _90144 t x). Qed.
Lemma lem3474168 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term80 _90144 t x) = (term239 _90144 t x).
Proof. exact (MK_COMB (@lem3474159) (@lem3474167 _90144 t x)). Qed.
Lemma lem3474169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474174 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474175 {_90144 : Type'} (f : type686 _90144) (x : _90144 -> Prop) : (f x) = (@I ((_90144 -> Prop) -> Prop) f x).
Proof. exact (@lem3474174 (_90144 -> Prop) Prop f x). Qed.
Lemma lem3474177 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (s t) = (@I ((_90144 -> Prop) -> Prop) s t).
Proof. exact (@lem3474175 _90144 s t). Qed.
Lemma lem3474178 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term244 _90144 s t) = (term245 _90144 s t).
Proof. exact (MK_COMB (@lem3474169) (@lem3474177 _90144 s t)). Qed.
Lemma lem3474179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474180 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : (term141 _90144 s t) = (term246 _90144 s t).
Proof. exact (MK_COMB (@lem3474179) (@lem3474178 _90144 s t)). Qed.
Lemma lem3474181 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term121 _90144 s t x) = (term247 _90144 s t x).
Proof. exact (MK_COMB (@lem3474180 _90144 s t) (@lem3474168 _90144 t x)). Qed.
Lemma lem3474182 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term129 _90144 s x) = (term248 _90144 s x).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3474181 _90144 s t x)). Qed.
Lemma lem3474183 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3474184 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term130 _90144 s x) = (term249 _90144 s x).
Proof. exact (MK_COMB (@lem3474183 _90144) (@lem3474182 _90144 s x)). Qed.
Lemma lem3474185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474186 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term133 _90144 s x) = (term250 _90144 s x).
Proof. exact (MK_COMB (@lem3474185) (@lem3474184 _90144 s x)). Qed.
Lemma lem3474187 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term135 _90144 s t x) = (term251 _90144 s t x).
Proof. exact (MK_COMB (@lem3474186 _90144 s x) (@lem3474158 _90144 t x)). Qed.
Lemma lem3474188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474189 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term153 _90144 s t x) = (term252 _90144 s t x).
Proof. exact (MK_COMB (@lem3474188) (@lem3474187 _90144 s t x)). Qed.
Lemma lem3474190 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term209 _90144 s t' t x) = (term253 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474189 _90144 s t x) (@lem3474150 _90144 s t' t x)). Qed.
Lemma lem3474195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474196 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474195 _90144 Prop f x). Qed.
Lemma lem3474198 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (t x) = (@I (_90144 -> Prop) t x).
Proof. exact (@lem3474196 _90144 t x). Qed.
Lemma lem3474199 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474205 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474204 _90144 Prop f x). Qed.
Lemma lem3474207 {_90144 : Type'} (x : _90144 -> Prop) (x' : _90144) : (x x') = (@I (_90144 -> Prop) x x').
Proof. exact (@lem3474205 _90144 x x'). Qed.
Lemma lem3474208 {_90144 : Type'} (x : _90144 -> Prop) (x' : _90144) : (term80 _90144 x x') = (term239 _90144 x x').
Proof. exact (MK_COMB (@lem3474199) (@lem3474207 _90144 x x')). Qed.
Lemma lem3474209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474210 {_90144 : Type'} (x : _90144 -> Prop) (x' : _90144) : (term137 _90144 x x') = (term254 _90144 x x').
Proof. exact (MK_COMB (@lem3474209) (@lem3474208 _90144 x x')). Qed.
Lemma lem3474211 {_90144 : Type'} (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term139 _90144 x t x') = (term255 _90144 x t x').
Proof. exact (MK_COMB (@lem3474210 _90144 x x') (@lem3474198 _90144 t x')). Qed.
Lemma lem3474212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474217 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474218 {_90144 : Type'} (f : type686 _90144) (x : _90144 -> Prop) : (f x) = (@I ((_90144 -> Prop) -> Prop) f x).
Proof. exact (@lem3474217 (_90144 -> Prop) Prop f x). Qed.
Lemma lem3474220 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) : (s x) = (@I ((_90144 -> Prop) -> Prop) s x).
Proof. exact (@lem3474218 _90144 s x). Qed.
Lemma lem3474221 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) : (term244 _90144 s x) = (term245 _90144 s x).
Proof. exact (MK_COMB (@lem3474212) (@lem3474220 _90144 s x)). Qed.
Lemma lem3474222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474223 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) : (term141 _90144 s x) = (term246 _90144 s x).
Proof. exact (MK_COMB (@lem3474222) (@lem3474221 _90144 s x)). Qed.
Lemma lem3474224 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term143 _90144 s x t x') = (term256 _90144 s x t x').
Proof. exact (MK_COMB (@lem3474223 _90144 s x) (@lem3474211 _90144 x t x')). Qed.
Lemma lem3474225 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term150 _90144 s t x) = (term257 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3474224 _90144 s x' t x)). Qed.
Lemma lem3474226 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3474227 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term151 _90144 s t x) = (term258 _90144 s t x).
Proof. exact (MK_COMB (@lem3474226 _90144) (@lem3474225 _90144 s t x)). Qed.
Lemma lem3474228 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474233 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474234 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474233 _90144 Prop f x). Qed.
Lemma lem3474236 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (t x) = (@I (_90144 -> Prop) t x).
Proof. exact (@lem3474234 _90144 t x). Qed.
Lemma lem3474237 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term80 _90144 t x) = (term239 _90144 t x).
Proof. exact (MK_COMB (@lem3474228) (@lem3474236 _90144 t x)). Qed.
Lemma lem3474242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474243 {_90144 : Type'} (f : _90144 -> Prop) (x : _90144) : (f x) = (@I (_90144 -> Prop) f x).
Proof. exact (@lem3474242 _90144 Prop f x). Qed.
Lemma lem3474245 {_90144 : Type'} (t' : _90144 -> Prop) (x : _90144) : (t' x) = (@I (_90144 -> Prop) t' x).
Proof. exact (@lem3474243 _90144 t' x). Qed.
Lemma lem3474250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3474251 {_90144 : Type'} (f : type686 _90144) (x : _90144 -> Prop) : (f x) = (@I ((_90144 -> Prop) -> Prop) f x).
Proof. exact (@lem3474250 (_90144 -> Prop) Prop f x). Qed.
Lemma lem3474253 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) : (s t') = (@I ((_90144 -> Prop) -> Prop) s t').
Proof. exact (@lem3474251 _90144 s t'). Qed.
Lemma lem3474254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474255 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) : (term71 _90144 s t') = (term242 _90144 s t').
Proof. exact (MK_COMB (@lem3474254) (@lem3474253 _90144 s t')). Qed.
Lemma lem3474256 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (x : _90144) : (term73 _90144 s t' x) = (term259 _90144 s t' x).
Proof. exact (MK_COMB (@lem3474255 _90144 s t') (@lem3474245 _90144 t' x)). Qed.
Lemma lem3474257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474258 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (x : _90144) : (term174 _90144 s t' x) = (term260 _90144 s t' x).
Proof. exact (MK_COMB (@lem3474257) (@lem3474256 _90144 s t' x)). Qed.
Lemma lem3474259 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term176 _90144 s t' t x) = (term261 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474258 _90144 s t' x) (@lem3474237 _90144 t x)). Qed.
Lemma lem3474260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474261 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term191 _90144 s t' t x) = (term262 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474260) (@lem3474259 _90144 s t' t x)). Qed.
Lemma lem3474262 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term193 _90144 t' s t x) = (term263 _90144 t' s t x).
Proof. exact (MK_COMB (@lem3474261 _90144 s t' t x) (@lem3474227 _90144 s t x)). Qed.
Lemma lem3474263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3474264 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term230 _90144 t' s t x) = (term264 _90144 t' s t x).
Proof. exact (MK_COMB (@lem3474263) (@lem3474262 _90144 t' s t x)). Qed.
Lemma lem3474265 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term232 _90144 s t' t x) = (term265 _90144 s t' t x).
Proof. exact (MK_COMB (@lem3474264 _90144 t' s t x) (@lem3474190 _90144 s t' t x)). Qed.
Lemma lem3474266 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term232 _90144 s t' t x) : term265 _90144 s t' t x.
Proof. exact (EQ_MP (@lem3474265 _90144 s t' t x) (@lem3474118 _90144 s t' t x h1)). Qed.
Lemma lem3474267 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term263 _90144 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3474268 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term253 _90144 s t' t x.
Proof. exact (h1). Qed.
Lemma lem3474269 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term258 _90144 s t x.
Proof. exact (proj2 (@lem3474267 _90144 t' s t x h1)). Qed.
Lemma lem3474270 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term261 _90144 s t' t x.
Proof. exact (proj1 (@lem3474267 _90144 t' s t x h1)). Qed.
Lemma lem3474272 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term259 _90144 s t' x.
Proof. exact (proj1 (@lem3474270 _90144 t' s t x h1)). Qed.
Lemma lem3474275 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term243 _90144 s t' t x.
Proof. exact (proj2 (@lem3474268 _90144 s t' t x h1)). Qed.
Lemma lem3474276 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term251 _90144 s t x.
Proof. exact (proj1 (@lem3474268 _90144 s t' t x h1)). Qed.
Lemma lem3474277 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term241 _90144 t' t x.
Proof. exact (proj2 (@lem3474275 _90144 s t' t x h1)). Qed.
Lemma lem3474281 {_90144 : Type'} (s : type686 _90144) (x : _90144) (h1 : term249 _90144 s x) : term249 _90144 s x.
Proof. exact (h1). Qed.
Lemma lem3474296 {_90144 : Type'} (s : type686 _90144) (x : _90144 -> Prop) (t : _90144 -> Prop) (x' : _90144) : (term256 _90144 s x t x') = (term256 _90144 s x t x').
Proof. exact (eq_refl (term256 _90144 s x t x')). Qed.
Lemma lem3474297 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term257 _90144 s t x) = (term257 _90144 s t x).
Proof. exact (fun_ext (fun x' : _90144 -> Prop => @lem3474296 _90144 s x' t x)). Qed.
Lemma lem3474298 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3474300 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term258 _90144 s t x) = (term258 _90144 s t x).
Proof. exact (MK_COMB (@lem3474298 _90144) (@lem3474297 _90144 s t x)). Qed.
Lemma lem3474301 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term258 _90144 s t x.
Proof. exact (EQ_MP (@lem3474300 _90144 s t x) (@lem3474269 _90144 t' s t x h1)). Qed.
Lemma lem3474333 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term247 _90144 s t x) = (term247 _90144 s t x).
Proof. exact (eq_refl (term247 _90144 s t x)). Qed.
Lemma lem3474334 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term248 _90144 s x) = (term248 _90144 s x).
Proof. exact (fun_ext (fun t : _90144 -> Prop => @lem3474333 _90144 s t x)). Qed.
Lemma lem3474335 {_90144 : Type'} : (@all (_90144 -> Prop)) = (@all (_90144 -> Prop)).
Proof. exact (eq_refl (@all (_90144 -> Prop))). Qed.
Lemma lem3474337 {_90144 : Type'} (s : type686 _90144) (x : _90144) : (term249 _90144 s x) = (term249 _90144 s x).
Proof. exact (MK_COMB (@lem3474335 _90144) (@lem3474334 _90144 s x)). Qed.
Lemma lem3474338 {_90144 : Type'} (s : type686 _90144) (x : _90144) (h1 : term249 _90144 s x) : term249 _90144 s x.
Proof. exact (EQ_MP (@lem3474337 _90144 s x) (@lem3474281 _90144 s x h1)). Qed.
Lemma lem3474354 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (h1 : @I (_90144 -> Prop) t x) : @I (_90144 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3474355 {_90144 : Type'} (_36675 : _90144 -> Prop) (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term266 _90144 s t x _36675.
Proof. exact (@lem3474301 _90144 t' s t x h1 _36675). Qed.
Lemma lem3474356 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term266 _90144 s t x _36675) = (term256 _90144 s _36675 t x).
Proof. exact (eq_refl (term266 _90144 s t x _36675)). Qed.
Lemma lem3474358 {_90144 : Type'} (_36676 : _90144 -> Prop) (s : type686 _90144) (x : _90144) (h1 : term249 _90144 s x) : term267 _90144 s x _36676.
Proof. exact (@lem3474338 _90144 s x h1 _36676). Qed.
Lemma lem3474359 {_90144 : Type'} (s : type686 _90144) (_36676 : _90144 -> Prop) (x : _90144) : (term267 _90144 s x _36676) = (term247 _90144 s _36676 x).
Proof. exact (eq_refl (term267 _90144 s x _36676)). Qed.
Lemma lem3474370 {_90144 : Type'} (_36675 : _90144 -> Prop) (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term256 _90144 s _36675 t x.
Proof. exact (EQ_MP (@lem3474356 _90144 s _36675 t x) (@lem3474355 _90144 _36675 t' s t x h1)). Qed.
Lemma lem3474372 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term239 _90144 t x.
Proof. exact (proj2 (@lem3474270 _90144 t' s t x h1)). Qed.
Lemma lem3474388 {_90144 : Type'} (_36676 : _90144 -> Prop) (s : type686 _90144) (x : _90144) (h1 : term249 _90144 s x) : term247 _90144 s _36676 x.
Proof. exact (EQ_MP (@lem3474359 _90144 s _36676 x) (@lem3474358 _90144 _36676 s x h1)). Qed.
Lemma lem3474394 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term239 _90144 t x.
Proof. exact (proj2 (@lem3474277 _90144 s t' t x h1)). Qed.
Lemma lem3474396 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (h1 : @I (_90144 -> Prop) t x) : @I (_90144 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3474398 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : @I ((_90144 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3474272 _90144 t' s t x h1)). Qed.
Lemma lem3474399 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term268 _90144 s t'.
Proof. exact (fun h0 : term245 _90144 s t' => @lem3474398 _90144 t' s t x h1). Qed.
Lemma lem3474401 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474402 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) : (term268 _90144 s t') = (@I ((_90144 -> Prop) -> Prop) s t').
Proof. exact (@lem3474401 (@I ((_90144 -> Prop) -> Prop) s t')). Qed.
Lemma lem3474403 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : @I ((_90144 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3474402 _90144 s t') (@lem3474399 _90144 t' s t x h1)). Qed.
Lemma lem3474405 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : @I (_90144 -> Prop) t' x.
Proof. exact (proj2 (@lem3474272 _90144 t' s t x h1)). Qed.
Lemma lem3474406 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term270 _90144 t' x.
Proof. exact (fun h0 : term239 _90144 t' x => @lem3474405 _90144 t' s t x h1). Qed.
Lemma lem3474408 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474409 {_90144 : Type'} (t' : _90144 -> Prop) (x : _90144) : (term270 _90144 t' x) = (@I (_90144 -> Prop) t' x).
Proof. exact (@lem3474408 (@I (_90144 -> Prop) t' x)). Qed.
Lemma lem3474410 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : @I (_90144 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3474409 _90144 t' x) (@lem3474406 _90144 t' s t x h1)). Qed.
Lemma lem3474416 (q : Prop) (p : Prop) (r : Prop) : (term271 p q r) = (term271 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3474417 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term256 _90144 s _36675 t x) = (term272 _90144 s _36675 t x).
Proof. exact (@lem3474416 (term239 _90144 _36675 x) (term245 _90144 s _36675) (@I (_90144 -> Prop) t x)). Qed.
Lemma lem3474431 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3474432 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term273 _90144 s _36675 t x) = (term274 _90144 t x s _36675).
Proof. exact (@lem3474431 (@I (_90144 -> Prop) t x) (term245 _90144 s _36675)). Qed.
Lemma lem3474438 {_90144 : Type'} (_36675 : _90144 -> Prop) (x : _90144) : (term254 _90144 _36675 x) = (term254 _90144 _36675 x).
Proof. exact (eq_refl (term254 _90144 _36675 x)). Qed.
Lemma lem3474439 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term272 _90144 s _36675 t x) = (term275 _90144 t x s _36675).
Proof. exact (MK_COMB (@lem3474438 _90144 _36675 x) (@lem3474432 _90144 t x s _36675)). Qed.
Lemma lem3474443 (q : Prop) (p : Prop) (r : Prop) : (term271 p q r) = (term271 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3474444 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term275 _90144 t x s _36675) = (term276 _90144 t x s _36675).
Proof. exact (@lem3474443 (@I (_90144 -> Prop) t x) (term239 _90144 _36675 x) (term245 _90144 s _36675)). Qed.
Lemma lem3474460 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term272 _90144 s _36675 t x) = (term276 _90144 t x s _36675).
Proof. exact (TRANS (@lem3474439 _90144 t x s _36675) (@lem3474444 _90144 t x s _36675)). Qed.
Lemma lem3474461 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term256 _90144 s _36675 t x) = (term276 _90144 t x s _36675).
Proof. exact (TRANS (@lem3474417 _90144 s _36675 t x) (@lem3474460 _90144 t x s _36675)). Qed.
Lemma lem3474462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474463 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term277 _90144 s _36675 t x) = (term278 _90144 t x s _36675).
Proof. exact (MK_COMB (@lem3474462) (@lem3474461 _90144 t x s _36675)). Qed.
Lemma lem3474477 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3474478 {_90144 : Type'} (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term247 _90144 s _36675 x) = (term279 _90144 x s _36675).
Proof. exact (@lem3474477 (term239 _90144 _36675 x) (term245 _90144 s _36675)). Qed.
Lemma lem3474484 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term280 _90144 t x) = (term280 _90144 t x).
Proof. exact (eq_refl (term280 _90144 t x)). Qed.
Lemma lem3474485 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : (term281 _90144 t s _36675 x) = (term276 _90144 t x s _36675).
Proof. exact (MK_COMB (@lem3474484 _90144 t x) (@lem3474478 _90144 x s _36675)). Qed.
Lemma lem3474496 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : ((term256 _90144 s _36675 t x) = (term281 _90144 t s _36675 x)) = ((term276 _90144 t x s _36675) = (term276 _90144 t x s _36675)).
Proof. exact (MK_COMB (@lem3474463 _90144 t x s _36675) (@lem3474485 _90144 t x s _36675)). Qed.
Lemma lem3474498 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3474499 (x : Prop) : (x = x) = True.
Proof. exact (@lem3474498 Prop x). Qed.
Lemma lem3474500 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (s : type686 _90144) (_36675 : _90144 -> Prop) : ((term276 _90144 t x s _36675) = (term276 _90144 t x s _36675)) = True.
Proof. exact (@lem3474499 (term276 _90144 t x s _36675)). Qed.
Lemma lem3474501 {_90144 : Type'} (t : _90144 -> Prop) (s : type686 _90144) (_36675 : _90144 -> Prop) (x : _90144) : ((term256 _90144 s _36675 t x) = (term281 _90144 t s _36675 x)) = True.
Proof. exact (TRANS (@lem3474496 _90144 t x s _36675) (@lem3474500 _90144 t x s _36675)). Qed.
Lemma lem3474502 {_90144 : Type'} (t : _90144 -> Prop) (s : type686 _90144) (_36675 : _90144 -> Prop) (x : _90144) : True = ((term256 _90144 s _36675 t x) = (term281 _90144 t s _36675 x)).
Proof. exact (SYM (@lem3474501 _90144 t s _36675 x)). Qed.
Lemma lem3474503 {_90144 : Type'} (t : _90144 -> Prop) (s : type686 _90144) (_36675 : _90144 -> Prop) (x : _90144) : (term256 _90144 s _36675 t x) = (term281 _90144 t s _36675 x).
Proof. exact (EQ_MP (@lem3474502 _90144 t s _36675 x) (@lem0)). Qed.
Lemma lem3474504 {_90144 : Type'} (_36675 : _90144 -> Prop) (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term281 _90144 t s _36675 x.
Proof. exact (EQ_MP (@lem3474503 _90144 t s _36675 x) (@lem3474370 _90144 _36675 t' s t x h1)). Qed.
Lemma lem3474506 (b : Prop) (a : Prop) : (a \/ b) = (term282 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3474507 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term281 _90144 t s _36675 x) = (term283 _90144 s _36675 t x).
Proof. exact (@lem3474506 (term247 _90144 s _36675 x) (@I (_90144 -> Prop) t x)). Qed.
Lemma lem3474509 (a : Prop) (b : Prop) : (term284 a b) = (term285 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3474510 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (x : _90144) : (term286 _90144 s _36675 x) = (term287 _90144 s _36675 x).
Proof. exact (@lem3474509 (term245 _90144 s _36675) (term239 _90144 _36675 x)). Qed.
Lemma lem3474512 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3474513 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) : (term288 _90144 s _36675) = (@I ((_90144 -> Prop) -> Prop) s _36675).
Proof. exact (@lem3474512 (@I ((_90144 -> Prop) -> Prop) s _36675)). Qed.
Lemma lem3474514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474515 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) : (term289 _90144 s _36675) = (term242 _90144 s _36675).
Proof. exact (MK_COMB (@lem3474514) (@lem3474513 _90144 s _36675)). Qed.
Lemma lem3474517 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3474518 {_90144 : Type'} (_36675 : _90144 -> Prop) (x : _90144) : (term290 _90144 _36675 x) = (@I (_90144 -> Prop) _36675 x).
Proof. exact (@lem3474517 (@I (_90144 -> Prop) _36675 x)). Qed.
Lemma lem3474519 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (x : _90144) : (term287 _90144 s _36675 x) = (term259 _90144 s _36675 x).
Proof. exact (MK_COMB (@lem3474515 _90144 s _36675) (@lem3474518 _90144 _36675 x)). Qed.
Lemma lem3474520 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (x : _90144) : (term286 _90144 s _36675 x) = (term259 _90144 s _36675 x).
Proof. exact (TRANS (@lem3474510 _90144 s _36675 x) (@lem3474519 _90144 s _36675 x)). Qed.
Lemma lem3474521 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3474522 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (x : _90144) : (term291 _90144 s _36675 x) = (term292 _90144 s _36675 x).
Proof. exact (MK_COMB (@lem3474521) (@lem3474520 _90144 s _36675 x)). Qed.
Lemma lem3474523 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (@I (_90144 -> Prop) t x) = (@I (_90144 -> Prop) t x).
Proof. exact (eq_refl (@I (_90144 -> Prop) t x)). Qed.
Lemma lem3474524 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term283 _90144 s _36675 t x) = (term293 _90144 s _36675 t x).
Proof. exact (MK_COMB (@lem3474522 _90144 s _36675 x) (@lem3474523 _90144 t x)). Qed.
Lemma lem3474525 {_90144 : Type'} (s : type686 _90144) (_36675 : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) : (term281 _90144 t s _36675 x) = (term293 _90144 s _36675 t x).
Proof. exact (TRANS (@lem3474507 _90144 s _36675 t x) (@lem3474524 _90144 s _36675 t x)). Qed.
Lemma lem3474527 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term259 _90144 s t' x.
Proof. exact (conj (@lem3474403 _90144 t' s t x h1) (@lem3474410 _90144 t' s t x h1)). Qed.
Lemma lem3474529 {_90144 : Type'} (_36675 : _90144 -> Prop) (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term293 _90144 s _36675 t x.
Proof. exact (EQ_MP (@lem3474525 _90144 s _36675 t x) (@lem3474504 _90144 _36675 t' s t x h1)). Qed.
Lemma lem3474530 {_90144 : Type'} (_36675 : _90144 -> Prop) (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term293 _90144 s _36675 t x.
Proof. exact (@lem3474529 _90144 _36675 t' s t x h1). Qed.
Lemma lem3474531 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term293 _90144 s t' t x.
Proof. exact (@lem3474530 _90144 t' t' s t x h1). Qed.
Lemma lem3474534 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : @I (_90144 -> Prop) t x.
Proof. exact (@lem3474531 _90144 t' s t x h1 (@lem3474527 _90144 t' s t x h1)). Qed.
Lemma lem3474535 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term270 _90144 t x.
Proof. exact (fun h0 : term239 _90144 t x => @lem3474534 _90144 t' s t x h1). Qed.
Lemma lem3474537 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474538 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term270 _90144 t x) = (@I (_90144 -> Prop) t x).
Proof. exact (@lem3474537 (@I (_90144 -> Prop) t x)). Qed.
Lemma lem3474539 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : @I (_90144 -> Prop) t x.
Proof. exact (EQ_MP (@lem3474538 _90144 t x) (@lem3474535 _90144 t' s t x h1)). Qed.
Lemma lem3474542 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3474544 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term239 _90144 t x) = (term294 _90144 t x).
Proof. exact (@lem3474542 (@I (_90144 -> Prop) t x)). Qed.
Lemma lem3474547 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term294 _90144 t x.
Proof. exact (EQ_MP (@lem3474544 _90144 t x) (@lem3474372 _90144 t' s t x h1)). Qed.
Lemma lem3474550 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : False.
Proof. exact (@lem3474547 _90144 t' s t x h1 (@lem3474539 _90144 t' s t x h1)). Qed.
Lemma lem3474551 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : term295.
Proof. exact (fun h0 : ~ False => @lem3474550 _90144 t' s t x h1). Qed.
Lemma lem3474553 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474554 : term295 = False.
Proof. exact (@lem3474553 False). Qed.
Lemma lem3474555 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term263 _90144 t' s t x) : False.
Proof. exact (EQ_MP (@lem3474554) (@lem3474551 _90144 t' s t x h1)). Qed.
Lemma lem3474557 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : @I ((_90144 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3474275 _90144 s t' t x h1)). Qed.
Lemma lem3474558 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term268 _90144 s t'.
Proof. exact (fun h0 : term245 _90144 s t' => @lem3474557 _90144 s t' t x h1). Qed.
Lemma lem3474560 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474561 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) : (term268 _90144 s t') = (@I ((_90144 -> Prop) -> Prop) s t').
Proof. exact (@lem3474560 (@I ((_90144 -> Prop) -> Prop) s t')). Qed.
Lemma lem3474562 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : @I ((_90144 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3474561 _90144 s t') (@lem3474558 _90144 s t' t x h1)). Qed.
Lemma lem3474564 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : @I (_90144 -> Prop) t' x.
Proof. exact (proj1 (@lem3474277 _90144 s t' t x h1)). Qed.
Lemma lem3474565 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term270 _90144 t' x.
Proof. exact (fun h0 : term239 _90144 t' x => @lem3474564 _90144 s t' t x h1). Qed.
Lemma lem3474567 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474568 {_90144 : Type'} (t' : _90144 -> Prop) (x : _90144) : (term270 _90144 t' x) = (@I (_90144 -> Prop) t' x).
Proof. exact (@lem3474567 (@I (_90144 -> Prop) t' x)). Qed.
Lemma lem3474569 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : @I (_90144 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3474568 _90144 t' x) (@lem3474565 _90144 s t' t x h1)). Qed.
Lemma lem3474571 (a : Prop) (b : Prop) : (term296 a b) = (term297 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3474572 {_90144 : Type'} (s : type686 _90144) (_36676 : _90144 -> Prop) (x : _90144) : (term247 _90144 s _36676 x) = (term298 _90144 s _36676 x).
Proof. exact (@lem3474571 (@I ((_90144 -> Prop) -> Prop) s _36676) (@I (_90144 -> Prop) _36676 x)). Qed.
Lemma lem3474574 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3474575 {_90144 : Type'} (s : type686 _90144) (_36676 : _90144 -> Prop) (x : _90144) : (term298 _90144 s _36676 x) = (term299 _90144 s _36676 x).
Proof. exact (@lem3474574 (term259 _90144 s _36676 x)). Qed.
Lemma lem3474576 {_90144 : Type'} (s : type686 _90144) (_36676 : _90144 -> Prop) (x : _90144) : (term247 _90144 s _36676 x) = (term299 _90144 s _36676 x).
Proof. exact (TRANS (@lem3474572 _90144 s _36676 x) (@lem3474575 _90144 s _36676 x)). Qed.
Lemma lem3474578 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term259 _90144 s t' x.
Proof. exact (conj (@lem3474562 _90144 s t' t x h1) (@lem3474569 _90144 s t' t x h1)). Qed.
Lemma lem3474580 {_90144 : Type'} (_36676 : _90144 -> Prop) (s : type686 _90144) (x : _90144) (h1 : term249 _90144 s x) : term299 _90144 s _36676 x.
Proof. exact (EQ_MP (@lem3474576 _90144 s _36676 x) (@lem3474388 _90144 _36676 s x h1)). Qed.
Lemma lem3474581 {_90144 : Type'} (_36676 : _90144 -> Prop) (s : type686 _90144) (x : _90144) (h1 : term249 _90144 s x) : term299 _90144 s _36676 x.
Proof. exact (@lem3474580 _90144 _36676 s x h1). Qed.
Lemma lem3474582 {_90144 : Type'} (t' : _90144 -> Prop) (s : type686 _90144) (x : _90144) (h1 : term249 _90144 s x) : term299 _90144 s t' x.
Proof. exact (@lem3474581 _90144 t' s x h1). Qed.
Lemma lem3474585 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term249 _90144 s x) (h2 : term253 _90144 s t' t x) : False.
Proof. exact (@lem3474582 _90144 t' s x h1 (@lem3474578 _90144 s t' t x h2)). Qed.
Lemma lem3474586 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term249 _90144 s x) (h2 : term253 _90144 s t' t x) : term295.
Proof. exact (fun h0 : ~ False => @lem3474585 _90144 s t' t x h1 h2). Qed.
Lemma lem3474588 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474589 : term295 = False.
Proof. exact (@lem3474588 False). Qed.
Lemma lem3474590 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term249 _90144 s x) (h2 : term253 _90144 s t' t x) : False.
Proof. exact (EQ_MP (@lem3474589) (@lem3474586 _90144 s t' t x h1 h2)). Qed.
Lemma lem3474592 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (h1 : @I (_90144 -> Prop) t x) : @I (_90144 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3474593 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (h1 : @I (_90144 -> Prop) t x) : term270 _90144 t x.
Proof. exact (fun h0 : term239 _90144 t x => @lem3474592 _90144 t x h1). Qed.
Lemma lem3474595 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474596 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term270 _90144 t x) = (@I (_90144 -> Prop) t x).
Proof. exact (@lem3474595 (@I (_90144 -> Prop) t x)). Qed.
Lemma lem3474597 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) (h1 : @I (_90144 -> Prop) t x) : @I (_90144 -> Prop) t x.
Proof. exact (EQ_MP (@lem3474596 _90144 t x) (@lem3474593 _90144 t x h1)). Qed.
Lemma lem3474600 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3474602 {_90144 : Type'} (t : _90144 -> Prop) (x : _90144) : (term239 _90144 t x) = (term294 _90144 t x).
Proof. exact (@lem3474600 (@I (_90144 -> Prop) t x)). Qed.
Lemma lem3474605 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : term294 _90144 t x.
Proof. exact (EQ_MP (@lem3474602 _90144 t x) (@lem3474394 _90144 s t' t x h1)). Qed.
Lemma lem3474608 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : False.
Proof. exact (@lem3474605 _90144 s t' t x h1 (@lem3474597 _90144 t x h2)). Qed.
Lemma lem3474609 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : term295.
Proof. exact (fun h0 : ~ False => @lem3474608 _90144 s t' t x h1 h2). Qed.
Lemma lem3474611 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3474612 : term295 = False.
Proof. exact (@lem3474611 False). Qed.
Lemma lem3474613 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3474612) (@lem3474609 _90144 s t' t x h1 h2)). Qed.
Lemma lem3474614 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : (@I (_90144 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_90144 -> Prop) t x => @lem3474613 _90144 s t' t x h1 h2) (fun h3 : False => @lem3474396 _90144 t x h2)). Qed.
Lemma lem3474615 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3474614 _90144 s t' t x h1 h2) (@lem3474396 _90144 t x h2)). Qed.
Lemma lem3474616 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : (@I (_90144 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_90144 -> Prop) t x => @lem3474615 _90144 s t' t x h1 h2) (fun h3 : False => @lem3474354 _90144 t x h2)). Qed.
Lemma lem3474617 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3474616 _90144 s t' t x h1 h2) (@lem3474354 _90144 t x h2)). Qed.
Lemma lem3474618 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : (@I (_90144 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_90144 -> Prop) t x => @lem3474617 _90144 s t' t x h1 h2) (fun h3 : False => @lem3474354 _90144 t x h2)). Qed.
Lemma lem3474619 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) (h2 : @I (_90144 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3474618 _90144 s t' t x h1 h2) (@lem3474354 _90144 t x h2)). Qed.
Lemma lem3474620 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term249 _90144 s x) (h2 : term253 _90144 s t' t x) : (term249 _90144 s x) = False.
Proof. exact (prop_ext (fun h3 : term249 _90144 s x => @lem3474590 _90144 s t' t x h1 h2) (fun h3 : False => @lem3474338 _90144 s x h1)). Qed.
Lemma lem3474621 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term249 _90144 s x) (h2 : term253 _90144 s t' t x) : False.
Proof. exact (EQ_MP (@lem3474620 _90144 s t' t x h1 h2) (@lem3474338 _90144 s x h1)). Qed.
Lemma lem3474622 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term253 _90144 s t' t x) : False.
Proof. exact (or_elim (@lem3474276 _90144 s t' t x h1) (fun h0 : term249 _90144 s x => @lem3474621 _90144 s t' t x h0 h1) (fun h0 : @I (_90144 -> Prop) t x => @lem3474619 _90144 s t' t x h1 h0)). Qed.
Lemma lem3474623 {_90144 : Type'} (s : type686 _90144) (t' : _90144 -> Prop) (t : _90144 -> Prop) (x : _90144) (h1 : term232 _90144 s t' t x) : False.
Proof. exact (or_elim (@lem3474266 _90144 s t' t x h1) (fun h0 : term263 _90144 t' s t x => @lem3474555 _90144 t' s t x h0) (fun h0 : term253 _90144 s t' t x => @lem3474622 _90144 s t' t x h0)). Qed.
Lemma lem3474624 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term119 _90144 s t x) : False.
Proof. exact (ex_elim (@lem3474117 _90144 s t x h1) (fun t' : _90144 -> Prop => fun h0 : term234 _90144 s t x t' => @lem3474623 _90144 s t' t x h0)). Qed.
Lemma lem3474625 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term119 _90144 s t x) : (term119 _90144 s t x) = False.
Proof. exact (prop_ext (fun h2 : term119 _90144 s t x => @lem3474624 _90144 s t x h1) (fun h2 : False => @lem3473758 _90144 s t x h1)). Qed.
Lemma lem3474626 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) (h1 : term119 _90144 s t x) : False.
Proof. exact (EQ_MP (@lem3474625 _90144 s t x h1) (@lem3473758 _90144 s t x h1)). Qed.
Lemma lem3474627 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : term118 _90144 s t x.
Proof. exact (fun h0 : term119 _90144 s t x => @lem3474626 _90144 s t x h0). Qed.
Lemma lem3474628 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) (x : _90144) : (term81 _90144 s t x) = (term102 _90144 s t x).
Proof. exact (EQ_MP (@lem3473757 _90144 s t x) (@lem3474627 _90144 s t x)). Qed.
Lemma lem3474633 {_90144 : Type'} (s : type686 _90144) (t : _90144 -> Prop) : term105 _90144 s t.
Proof. exact (fun x : _90144 => @lem3474628 _90144 s t x). Qed.
Lemma lem3474638 {_90144 : Type'} (s : type686 _90144) : term107 _90144 s.
Proof. exact (fun t : _90144 -> Prop => @lem3474633 _90144 s t). Qed.
Lemma lem3474643 {_90144 : Type'} : term109 _90144.
Proof. exact (fun s : type686 _90144 => @lem3474638 _90144 s). Qed.
Lemma lem3474644 {_90144 : Type'} : term111 _90144.
Proof. exact (EQ_MP (@lem3473753 _90144) (@lem3474643 _90144)). Qed.
Lemma lem3474646 {_90144 : Type'} : term111 _90144.
Proof. exact (@lem3473584 _90144 (@lem3474644 _90144)). Qed.
Lemma lem3474647 {_90144 : Type'} (h1 : term112 _90144) : False.
Proof. exact (@lem3474646 _90144 (@lem3473568 _90144 h1)). Qed.
Lemma lem3474648 {_90144 : Type'} (h1 : term112 _90144) : (term112 _90144) = False.
Proof. exact (prop_ext (fun h2 : term112 _90144 => @lem3474647 _90144 h1) (fun h2 : False => @lem3473568 _90144 h1)). Qed.
Lemma lem3474649 {_90144 : Type'} (h1 : term112 _90144) : False.
Proof. exact (EQ_MP (@lem3474648 _90144 h1) (@lem3473568 _90144 h1)). Qed.
Lemma lem3474650 {_90144 : Type'} : term111 _90144.
Proof. exact (fun h0 : term112 _90144 => @lem3474649 _90144 h0). Qed.
Lemma lem3474651 {_90144 : Type'} : term109 _90144.
Proof. exact (EQ_MP (@lem3473567 _90144) (@lem3474650 _90144)). Qed.
Lemma lem3474652 {_90144 : Type'} : term65 _90144.
Proof. exact (EQ_MP (@lem3473563 _90144) (@lem3474651 _90144)). Qed.
Lemma lem3474653 {_90144 : Type'} : term59 _90144.
Proof. exact (EQ_MP (@lem3473407 _90144) (@lem3474652 _90144)). Qed.
Lemma lem3474654 {_90144 : Type'} : term58 _90144.
Proof. exact (EQ_MP (@lem3473360 _90144) (@lem3474653 _90144)). Qed.
