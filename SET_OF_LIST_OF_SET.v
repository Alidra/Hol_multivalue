Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_OF_LIST_OF_SET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LIST_OF_SET_PROPERTIES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4786979 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4786980 {_110305 : Type'} : (term1 _110305) = (term2 _110305).
Proof. exact (@lem4786979 (term1 _110305)). Qed.
Lemma lem4786981 {_110305 : Type'} : (term2 _110305) = (term1 _110305).
Proof. exact (SYM (@lem4786980 _110305)). Qed.
Lemma lem4786982 {_110305 : Type'} (h1 : term3 _110305) : term3 _110305.
Proof. exact (h1). Qed.
Lemma lem4786983 {_110305 : Type'} : term4 _110305.
Proof. exact (@lem4786967 _110305). Qed.
Lemma lem4786989 {_110305 : Type'} (h1 : term5 _110305) : term5 _110305.
Proof. exact (h1). Qed.
Lemma lem4786990 {_110305 : Type'} : term6 _110305.
Proof. exact (fun h0 : term5 _110305 => @lem4786989 _110305 h0). Qed.
Lemma lem4786991 {_110305 : Type'} (h1 : term6 _110305) : term6 _110305.
Proof. exact (h1). Qed.
Lemma lem4786992 {_110305 : Type'} (h1 : term5 _110305) : term5 _110305.
Proof. exact (h1). Qed.
Lemma lem4786993 {_110305 : Type'} (h1 : term5 _110305) (h2 : term6 _110305) : term5 _110305.
Proof. exact (@lem4786991 _110305 h2 (@lem4786992 _110305 h1)). Qed.
Lemma lem4786994 {_110305 : Type'} (h1 : term5 _110305) : term7 _110305.
Proof. exact (fun h0 : term6 _110305 => @lem4786993 _110305 h1 h0). Qed.
Lemma lem4786995 {_110305 : Type'} (h1 : term6 _110305) : term6 _110305.
Proof. exact (h1). Qed.
Lemma lem4786996 {_110305 : Type'} (h1 : term5 _110305) (h2 : term6 _110305) : term5 _110305.
Proof. exact (@lem4786994 _110305 h1 (@lem4786995 _110305 h2)). Qed.
Lemma lem4786997 {_110305 : Type'} (h1 : term6 _110305) : term6 _110305.
Proof. exact (fun h0 : term5 _110305 => @lem4786996 _110305 h0 h1). Qed.
Lemma lem4786998 {_110305 : Type'} : term8 _110305.
Proof. exact (fun h0 : term6 _110305 => @lem4786997 _110305 h0). Qed.
Lemma lem4787001 {_110305 : Type'} : term6 _110305.
Proof. exact (@lem4786998 _110305 (@lem4786990 _110305)). Qed.
Lemma lem4787002 {_110305 : Type'} : term6 _110305.
Proof. exact (@lem4787001 _110305). Qed.
Lemma lem4787012 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4787013 {_110305 : Type'} : (term9 _110305) = (term10 _110305).
Proof. exact (@lem4787012 (term4 _110305)). Qed.
Lemma lem4787022 {_110305 : Type'} : (term11 _110305) = (term11 _110305).
Proof. exact (eq_refl (term11 _110305)). Qed.
Lemma lem4787029 {_110305 : Type'} : (term5 _110305) = (term12 _110305).
Proof. exact (MK_COMB (@lem4787022 _110305) (@lem4787013 _110305)). Qed.
Lemma lem4787038 {_110305 : Type'} (s : _110305 -> Prop) : (term13 _110305 s) = (term13 _110305 s).
Proof. exact (eq_refl (term13 _110305 s)). Qed.
Lemma lem4787039 {_110305 : Type'} : (term14 _110305) = (term14 _110305).
Proof. exact (fun_ext (fun s : _110305 -> Prop => @lem4787038 _110305 s)). Qed.
Lemma lem4787040 {_110305 : Type'} : (@all (_110305 -> Prop)) = (@all (_110305 -> Prop)).
Proof. exact (eq_refl (@all (_110305 -> Prop))). Qed.
Lemma lem4787041 {_110305 : Type'} : (term4 _110305) = (term4 _110305).
Proof. exact (MK_COMB (@lem4787040 _110305) (@lem4787039 _110305)). Qed.
Lemma lem4787042 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4787043 {_110305 : Type'} : (term10 _110305) = (term10 _110305).
Proof. exact (MK_COMB (@lem4787042) (@lem4787041 _110305)). Qed.
Lemma lem4787048 {_110305 : Type'} (s : _110305 -> Prop) : (term15 _110305 s) = (term15 _110305 s).
Proof. exact (eq_refl (term15 _110305 s)). Qed.
Lemma lem4787049 {_110305 : Type'} : (term16 _110305) = (term16 _110305).
Proof. exact (fun_ext (fun s : _110305 -> Prop => @lem4787048 _110305 s)). Qed.
Lemma lem4787050 {_110305 : Type'} : (@all (_110305 -> Prop)) = (@all (_110305 -> Prop)).
Proof. exact (eq_refl (@all (_110305 -> Prop))). Qed.
Lemma lem4787051 {_110305 : Type'} : (term1 _110305) = (term1 _110305).
Proof. exact (MK_COMB (@lem4787050 _110305) (@lem4787049 _110305)). Qed.
Lemma lem4787052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4787053 {_110305 : Type'} : (term3 _110305) = (term3 _110305).
Proof. exact (MK_COMB (@lem4787052) (@lem4787051 _110305)). Qed.
Lemma lem4787054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4787055 {_110305 : Type'} : (term11 _110305) = (term11 _110305).
Proof. exact (MK_COMB (@lem4787054) (@lem4787053 _110305)). Qed.
Lemma lem4787056 {_110305 : Type'} : (term12 _110305) = (term12 _110305).
Proof. exact (MK_COMB (@lem4787055 _110305) (@lem4787043 _110305)). Qed.
Lemma lem4787079 {_110305 : Type'} : (term5 _110305) = (term12 _110305).
Proof. exact (TRANS (@lem4787029 _110305) (@lem4787056 _110305)). Qed.
Lemma lem4787080 {_110305 : Type'} : (term12 _110305) = (term5 _110305).
Proof. exact (SYM (@lem4787079 _110305)). Qed.
Lemma lem4787081 {_110305 : Type'} (h1 : term3 _110305) : term3 _110305.
Proof. exact (h1). Qed.
Lemma lem4787082 {_110305 : Type'} (h1 : term4 _110305) : term4 _110305.
Proof. exact (h1). Qed.
Lemma lem4787089 {_110305 : Type'} (s : _110305 -> Prop) : (term17 _110305 s) = (term18 _110305 s).
Proof. exact (@lem17362 (@FINITE _110305 s) ((term19 _110305 s) = s)). Qed.
Lemma lem4787090 {_110305 : Type'} (P : type686 _110305) : (term20 _110305 P) = (term21 _110305 P).
Proof. exact (@lem18392 (_110305 -> Prop) P). Qed.
Lemma lem4787091 {_110305 : Type'} : (term3 _110305) = (term22 _110305).
Proof. exact (@lem4787090 _110305 (term16 _110305)). Qed.
Lemma lem4787092 {_110305 : Type'} (s : _110305 -> Prop) : (term23 _110305 s) = (term15 _110305 s).
Proof. exact (eq_refl (term23 _110305 s)). Qed.
Lemma lem4787093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4787094 {_110305 : Type'} (s : _110305 -> Prop) : (term24 _110305 s) = (term17 _110305 s).
Proof. exact (MK_COMB (@lem4787093) (@lem4787092 _110305 s)). Qed.
Lemma lem4787095 {_110305 : Type'} (s : _110305 -> Prop) : (term24 _110305 s) = (term18 _110305 s).
Proof. exact (TRANS (@lem4787094 _110305 s) (@lem4787089 _110305 s)). Qed.
Lemma lem4787096 {_110305 : Type'} : (term25 _110305) = (term26 _110305).
Proof. exact (fun_ext (fun s : _110305 -> Prop => @lem4787095 _110305 s)). Qed.
Lemma lem4787097 {_110305 : Type'} : (@ex (_110305 -> Prop)) = (@ex (_110305 -> Prop)).
Proof. exact (eq_refl (@ex (_110305 -> Prop))). Qed.
Lemma lem4787098 {_110305 : Type'} : (term22 _110305) = (term27 _110305).
Proof. exact (MK_COMB (@lem4787097 _110305) (@lem4787096 _110305)). Qed.
Lemma lem4787131 {_110305 : Type'} : (term3 _110305) = (term27 _110305).
Proof. exact (TRANS (@lem4787091 _110305) (@lem4787098 _110305)). Qed.
Lemma lem4787132 {_110305 : Type'} (h1 : term3 _110305) : term27 _110305.
Proof. exact (EQ_MP (@lem4787131 _110305) (@lem4787081 _110305 h1)). Qed.
Lemma lem4787143 {_110305 : Type'} (s : _110305 -> Prop) : (term13 _110305 s) = (term28 _110305 s).
Proof. exact (@lem17265 (@FINITE _110305 s) (term29 _110305 s)). Qed.
Lemma lem4787144 {_110305 : Type'} : (term14 _110305) = (term30 _110305).
Proof. exact (fun_ext (fun s : _110305 -> Prop => @lem4787143 _110305 s)). Qed.
Lemma lem4787145 {_110305 : Type'} : (@all (_110305 -> Prop)) = (@all (_110305 -> Prop)).
Proof. exact (eq_refl (@all (_110305 -> Prop))). Qed.
Lemma lem4787198 {_110305 : Type'} : (term4 _110305) = (term31 _110305).
Proof. exact (MK_COMB (@lem4787145 _110305) (@lem4787144 _110305)). Qed.
Lemma lem4787199 {_110305 : Type'} (h1 : term4 _110305) : term31 _110305.
Proof. exact (EQ_MP (@lem4787198 _110305) (@lem4787082 _110305 h1)). Qed.
Lemma lem4787231 {_110305 : Type'} (s : _110305 -> Prop) : (term28 _110305 s) = (term28 _110305 s).
Proof. exact (eq_refl (term28 _110305 s)). Qed.
Lemma lem4787232 {_110305 : Type'} : (term30 _110305) = (term30 _110305).
Proof. exact (fun_ext (fun s : _110305 -> Prop => @lem4787231 _110305 s)). Qed.
Lemma lem4787233 {_110305 : Type'} : (@all (_110305 -> Prop)) = (@all (_110305 -> Prop)).
Proof. exact (eq_refl (@all (_110305 -> Prop))). Qed.
Lemma lem4787234 {_110305 : Type'} : (term31 _110305) = (term31 _110305).
Proof. exact (MK_COMB (@lem4787233 _110305) (@lem4787232 _110305)). Qed.
Lemma lem4787235 {_110305 : Type'} (h1 : term4 _110305) : term31 _110305.
Proof. exact (EQ_MP (@lem4787234 _110305) (@lem4787199 _110305 h1)). Qed.
Lemma lem4787253 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term18 _110305 s) : term18 _110305 s.
Proof. exact (h1). Qed.
Lemma lem4787273 {_110305 : Type'} (s : _110305 -> Prop) : (term28 _110305 s) = (term32 _110305 s).
Proof. exact (@lem19490 ((term19 _110305 s) = s) (term33 _110305 s) ((term34 _110305 s) = (@CARD _110305 s))). Qed.
Lemma lem4787274 {_110305 : Type'} : (term30 _110305) = (term35 _110305).
Proof. exact (fun_ext (fun s : _110305 -> Prop => @lem4787273 _110305 s)). Qed.
Lemma lem4787275 {_110305 : Type'} : (@all (_110305 -> Prop)) = (@all (_110305 -> Prop)).
Proof. exact (eq_refl (@all (_110305 -> Prop))). Qed.
Lemma lem4787277 {_110305 : Type'} : (term31 _110305) = (term36 _110305).
Proof. exact (MK_COMB (@lem4787275 _110305) (@lem4787274 _110305)). Qed.
Lemma lem4787278 {_110305 : Type'} (h1 : term4 _110305) : term36 _110305.
Proof. exact (EQ_MP (@lem4787277 _110305) (@lem4787235 _110305 h1)). Qed.
Lemma lem4787287 {_110305 : Type'} (_59123 : _110305 -> Prop) (h1 : term4 _110305) : term37 _110305 _59123.
Proof. exact (@lem4787278 _110305 h1 _59123). Qed.
Lemma lem4787288 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term37 _110305 _59123) = (term32 _110305 _59123).
Proof. exact (eq_refl (term37 _110305 _59123)). Qed.
Lemma lem4787289 {_110305 : Type'} (_59123 : _110305 -> Prop) (h1 : term4 _110305) : term32 _110305 _59123.
Proof. exact (EQ_MP (@lem4787288 _110305 _59123) (@lem4787287 _110305 _59123 h1)). Qed.
Lemma lem4787295 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term18 _110305 s) : term38 _110305 s.
Proof. exact (proj2 (@lem4787253 _110305 s h1)). Qed.
Lemma lem4787301 {_110305 : Type'} (_59123 : _110305 -> Prop) (h1 : term4 _110305) : term39 _110305 _59123.
Proof. exact (proj1 (@lem4787289 _110305 _59123 h1)). Qed.
Lemma lem4787359 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term18 _110305 s) : @FINITE _110305 s.
Proof. exact (proj1 (@lem4787253 _110305 s h1)). Qed.
Lemma lem4787360 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term18 _110305 s) : term40 _110305 s.
Proof. exact (fun h0 : term33 _110305 s => @lem4787359 _110305 s h1). Qed.
Lemma lem4787362 (p : Prop) : (term41 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4787363 {_110305 : Type'} (s : _110305 -> Prop) : (term40 _110305 s) = (@FINITE _110305 s).
Proof. exact (@lem4787362 (@FINITE _110305 s)). Qed.
Lemma lem4787364 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term18 _110305 s) : @FINITE _110305 s.
Proof. exact (EQ_MP (@lem4787363 _110305 s) (@lem4787360 _110305 s h1)). Qed.
Lemma lem4787370 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4787371 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term39 _110305 _59123) = (term42 _110305 _59123).
Proof. exact (@lem4787370 ((term19 _110305 _59123) = _59123) (term33 _110305 _59123)). Qed.
Lemma lem4787379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4787380 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term43 _110305 _59123) = (term44 _110305 _59123).
Proof. exact (MK_COMB (@lem4787379) (@lem4787371 _110305 _59123)). Qed.
Lemma lem4787388 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term42 _110305 _59123) = (term42 _110305 _59123).
Proof. exact (eq_refl (term42 _110305 _59123)). Qed.
Lemma lem4787389 {_110305 : Type'} (_59123 : _110305 -> Prop) : ((term39 _110305 _59123) = (term42 _110305 _59123)) = ((term42 _110305 _59123) = (term42 _110305 _59123)).
Proof. exact (MK_COMB (@lem4787380 _110305 _59123) (@lem4787388 _110305 _59123)). Qed.
Lemma lem4787391 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4787392 (x : Prop) : (x = x) = True.
Proof. exact (@lem4787391 Prop x). Qed.
Lemma lem4787393 {_110305 : Type'} (_59123 : _110305 -> Prop) : ((term42 _110305 _59123) = (term42 _110305 _59123)) = True.
Proof. exact (@lem4787392 (term42 _110305 _59123)). Qed.
Lemma lem4787394 {_110305 : Type'} (_59123 : _110305 -> Prop) : ((term39 _110305 _59123) = (term42 _110305 _59123)) = True.
Proof. exact (TRANS (@lem4787389 _110305 _59123) (@lem4787393 _110305 _59123)). Qed.
Lemma lem4787395 {_110305 : Type'} (_59123 : _110305 -> Prop) : True = ((term39 _110305 _59123) = (term42 _110305 _59123)).
Proof. exact (SYM (@lem4787394 _110305 _59123)). Qed.
Lemma lem4787396 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term39 _110305 _59123) = (term42 _110305 _59123).
Proof. exact (EQ_MP (@lem4787395 _110305 _59123) (@lem0)). Qed.
Lemma lem4787397 {_110305 : Type'} (_59123 : _110305 -> Prop) (h1 : term4 _110305) : term42 _110305 _59123.
Proof. exact (EQ_MP (@lem4787396 _110305 _59123) (@lem4787301 _110305 _59123 h1)). Qed.
Lemma lem4787399 (b : Prop) (a : Prop) : (a \/ b) = (term45 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4787400 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term42 _110305 _59123) = (term46 _110305 _59123).
Proof. exact (@lem4787399 (term33 _110305 _59123) ((term19 _110305 _59123) = _59123)). Qed.
Lemma lem4787402 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4787403 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term48 _110305 _59123) = (@FINITE _110305 _59123).
Proof. exact (@lem4787402 (@FINITE _110305 _59123)). Qed.
Lemma lem4787404 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4787405 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term49 _110305 _59123) = (term50 _110305 _59123).
Proof. exact (MK_COMB (@lem4787404) (@lem4787403 _110305 _59123)). Qed.
Lemma lem4787406 {_110305 : Type'} (_59123 : _110305 -> Prop) : ((term19 _110305 _59123) = _59123) = ((term19 _110305 _59123) = _59123).
Proof. exact (eq_refl ((term19 _110305 _59123) = _59123)). Qed.
Lemma lem4787407 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term46 _110305 _59123) = (term15 _110305 _59123).
Proof. exact (MK_COMB (@lem4787405 _110305 _59123) (@lem4787406 _110305 _59123)). Qed.
Lemma lem4787408 {_110305 : Type'} (_59123 : _110305 -> Prop) : (term42 _110305 _59123) = (term15 _110305 _59123).
Proof. exact (TRANS (@lem4787400 _110305 _59123) (@lem4787407 _110305 _59123)). Qed.
Lemma lem4787411 {_110305 : Type'} (_59123 : _110305 -> Prop) (h1 : term4 _110305) : term15 _110305 _59123.
Proof. exact (EQ_MP (@lem4787408 _110305 _59123) (@lem4787397 _110305 _59123 h1)). Qed.
Lemma lem4787412 {_110305 : Type'} (_59123 : _110305 -> Prop) (h1 : term4 _110305) : term15 _110305 _59123.
Proof. exact (@lem4787411 _110305 _59123 h1). Qed.
Lemma lem4787413 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) : term15 _110305 s.
Proof. exact (@lem4787412 _110305 s h1). Qed.
Lemma lem4787416 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : (term19 _110305 s) = s.
Proof. exact (@lem4787413 _110305 s h1 (@lem4787364 _110305 s h2)). Qed.
Lemma lem4787417 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : term51 _110305 s.
Proof. exact (fun h0 : term38 _110305 s => @lem4787416 _110305 s h1 h2). Qed.
Lemma lem4787419 (p : Prop) : (term41 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4787420 {_110305 : Type'} (s : _110305 -> Prop) : (term51 _110305 s) = ((term19 _110305 s) = s).
Proof. exact (@lem4787419 ((term19 _110305 s) = s)). Qed.
Lemma lem4787421 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : (term19 _110305 s) = s.
Proof. exact (EQ_MP (@lem4787420 _110305 s) (@lem4787417 _110305 s h1 h2)). Qed.
Lemma lem4787424 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4787426 {_110305 : Type'} (s : _110305 -> Prop) : (term38 _110305 s) = (term52 _110305 s).
Proof. exact (@lem4787424 ((term19 _110305 s) = s)). Qed.
Lemma lem4787429 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term18 _110305 s) : term52 _110305 s.
Proof. exact (EQ_MP (@lem4787426 _110305 s) (@lem4787295 _110305 s h1)). Qed.
Lemma lem4787432 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : False.
Proof. exact (@lem4787429 _110305 s h2 (@lem4787421 _110305 s h1 h2)). Qed.
Lemma lem4787433 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : term53.
Proof. exact (fun h0 : ~ False => @lem4787432 _110305 s h1 h2). Qed.
Lemma lem4787435 (p : Prop) : (term41 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4787436 : term53 = False.
Proof. exact (@lem4787435 False). Qed.
Lemma lem4787437 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : False.
Proof. exact (EQ_MP (@lem4787436) (@lem4787433 _110305 s h1 h2)). Qed.
Lemma lem4787438 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : (term18 _110305 s) = False.
Proof. exact (prop_ext (fun h3 : term18 _110305 s => @lem4787437 _110305 s h1 h2) (fun h3 : False => @lem4787253 _110305 s h2)). Qed.
Lemma lem4787439 {_110305 : Type'} (s : _110305 -> Prop) (h1 : term4 _110305) (h2 : term18 _110305 s) : False.
Proof. exact (EQ_MP (@lem4787438 _110305 s h1 h2) (@lem4787253 _110305 s h2)). Qed.
Lemma lem4787440 {_110305 : Type'} (h1 : term4 _110305) (h2 : term3 _110305) : False.
Proof. exact (ex_elim (@lem4787132 _110305 h2) (fun s : _110305 -> Prop => fun h0 : term26 _110305 s => @lem4787439 _110305 s h1 h0)). Qed.
Lemma lem4787441 {_110305 : Type'} (h1 : term3 _110305) : term9 _110305.
Proof. exact (fun h0 : term4 _110305 => @lem4787440 _110305 h0 h1). Qed.
Lemma lem4787442 {_110305 : Type'} : (term9 _110305) = (term10 _110305).
Proof. exact (@lem69 (term4 _110305)). Qed.
Lemma lem4787443 {_110305 : Type'} (h1 : term3 _110305) : term10 _110305.
Proof. exact (EQ_MP (@lem4787442 _110305) (@lem4787441 _110305 h1)). Qed.
Lemma lem4787444 {_110305 : Type'} : term12 _110305.
Proof. exact (fun h0 : term3 _110305 => @lem4787443 _110305 h0). Qed.
Lemma lem4787445 {_110305 : Type'} : term5 _110305.
Proof. exact (EQ_MP (@lem4787080 _110305) (@lem4787444 _110305)). Qed.
Lemma lem4787447 {_110305 : Type'} : term5 _110305.
Proof. exact (@lem4787002 _110305 (@lem4787445 _110305)). Qed.
Lemma lem4787448 {_110305 : Type'} (h1 : term3 _110305) : term9 _110305.
Proof. exact (@lem4787447 _110305 (@lem4786982 _110305 h1)). Qed.
Lemma lem4787449 {_110305 : Type'} (h1 : term3 _110305) : False.
Proof. exact (@lem4787448 _110305 h1 (@lem4786983 _110305)). Qed.
Lemma lem4787450 {_110305 : Type'} (h1 : term3 _110305) : (term3 _110305) = False.
Proof. exact (prop_ext (fun h2 : term3 _110305 => @lem4787449 _110305 h1) (fun h2 : False => @lem4786982 _110305 h1)). Qed.
Lemma lem4787451 {_110305 : Type'} (h1 : term3 _110305) : False.
Proof. exact (EQ_MP (@lem4787450 _110305 h1) (@lem4786982 _110305 h1)). Qed.
Lemma lem4787452 {_110305 : Type'} : term2 _110305.
Proof. exact (fun h0 : term3 _110305 => @lem4787451 _110305 h0). Qed.
Lemma lem4787453 {_110305 : Type'} : term1 _110305.
Proof. exact (EQ_MP (@lem4786981 _110305) (@lem4787452 _110305)). Qed.
