Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm52751_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm51886_spec.
Require Import thm51887_spec.
Require Import thm51892_spec.
Require Import thm51893_spec.
Lemma lem52350 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term0 A B f g).
Proof. exact (EQ_MP (@lem51893 A B f g) (@lem51892 A B f g)). Qed.
Lemma lem52351 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (g : type1218 _5310 _5326 _5330 _5333 _5334) : (f = g) = (term1 _5310 _5326 _5330 _5333 _5334 f g).
Proof. exact (@lem52350 (type1655 _5326 _5330 _5333 _5334) _5310 f g). Qed.
Lemma lem52352 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : ((term2 _5310 _5326 _5330 _5333 _5334 f) = f) = (term3 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (@lem52351 _5310 _5326 _5330 _5333 _5334 (term2 _5310 _5326 _5330 _5333 _5334 f) f). Qed.
Lemma lem52358 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = (term5 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51887 _5106 _5107 P) (@lem51886 _5106 _5107 P)). Qed.
Lemma lem52359 {_5326 _5330 _5333 _5334 : Type'} (P : type1195 _5326 _5330 _5333 _5334) : (term6 _5326 _5330 _5333 _5334 P) = (term7 _5326 _5330 _5333 _5334 P).
Proof. exact (@lem52358 (type1657 _5330 _5333 _5334) _5326 P). Qed.
Lemma lem52360 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term8 _5310 _5326 _5330 _5333 _5334 f) = (term9 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (@lem52359 _5326 _5330 _5333 _5334 (term10 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52361 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (x : type1655 _5326 _5330 _5333 _5334) : (term11 _5310 _5326 _5330 _5333 _5334 f x) = ((term12 _5310 _5326 _5330 _5333 _5334 f x) = (f x)).
Proof. exact (eq_refl (term11 _5310 _5326 _5330 _5333 _5334 f x)). Qed.
Lemma lem52362 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term13 _5310 _5326 _5330 _5333 _5334 f) = (term10 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (fun_ext (fun x : type1655 _5326 _5330 _5333 _5334 => @lem52361 _5310 _5326 _5330 _5333 _5334 f x)). Qed.
Lemma lem52363 {_5326 _5330 _5333 _5334 : Type'} : (@all (prod _5326 (prod _5330 (prod _5334 _5333)))) = (@all (prod _5326 (prod _5330 (prod _5334 _5333)))).
Proof. exact (eq_refl (@all (prod _5326 (prod _5330 (prod _5334 _5333))))). Qed.
Lemma lem52364 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term8 _5310 _5326 _5330 _5333 _5334 f) = (term3 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (MK_COMB (@lem52363 _5326 _5330 _5333 _5334) (@lem52362 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem52366 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term14 _5310 _5326 _5330 _5333 _5334 f) = (term15 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (MK_COMB (@lem52365) (@lem52364 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52367 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p2 : type1657 _5330 _5333 _5334) : (term16 _5310 _5326 _5330 _5333 _5334 f p1 p2) = ((term17 _5310 _5326 _5330 _5333 _5334 f p1 p2) = (term18 _5310 _5326 _5330 _5333 _5334 f p1 p2)).
Proof. exact (eq_refl (term16 _5310 _5326 _5330 _5333 _5334 f p1 p2)). Qed.
Lemma lem52368 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term19 _5310 _5326 _5330 _5333 _5334 f p1) = (term20 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (fun_ext (fun p2 : type1657 _5330 _5333 _5334 => @lem52367 _5310 _5326 _5330 _5333 _5334 f p1 p2)). Qed.
Lemma lem52369 {_5330 _5333 _5334 : Type'} : (@all (prod _5330 (prod _5334 _5333))) = (@all (prod _5330 (prod _5334 _5333))).
Proof. exact (eq_refl (@all (prod _5330 (prod _5334 _5333)))). Qed.
Lemma lem52370 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term21 _5310 _5326 _5330 _5333 _5334 f p1) = (term22 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (MK_COMB (@lem52369 _5330 _5333 _5334) (@lem52368 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52371 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term23 _5310 _5326 _5330 _5333 _5334 f) = (term24 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (fun_ext (fun p1 : _5326 => @lem52370 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52372 {_5326 : Type'} : (@all _5326) = (@all _5326).
Proof. exact (eq_refl (@all _5326)). Qed.
Lemma lem52373 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term9 _5310 _5326 _5330 _5333 _5334 f) = (term25 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (MK_COMB (@lem52372 _5326) (@lem52371 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52374 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : ((term8 _5310 _5326 _5330 _5333 _5334 f) = (term9 _5310 _5326 _5330 _5333 _5334 f)) = ((term3 _5310 _5326 _5330 _5333 _5334 f) = (term25 _5310 _5326 _5330 _5333 _5334 f)).
Proof. exact (MK_COMB (@lem52366 _5310 _5326 _5330 _5333 _5334 f) (@lem52373 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52375 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term3 _5310 _5326 _5330 _5333 _5334 f) = (term25 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (EQ_MP (@lem52374 _5310 _5326 _5330 _5333 _5334 f) (@lem52360 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52382 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : ((term2 _5310 _5326 _5330 _5333 _5334 f) = f) = (term25 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (TRANS (@lem52352 _5310 _5326 _5330 _5333 _5334 f) (@lem52375 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52388 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = (term5 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51887 _5106 _5107 P) (@lem51886 _5106 _5107 P)). Qed.
Lemma lem52389 {_5330 _5333 _5334 : Type'} (P : type1202 _5330 _5333 _5334) : (term26 _5330 _5333 _5334 P) = (term27 _5330 _5333 _5334 P).
Proof. exact (@lem52388 (prod _5334 _5333) _5330 P). Qed.
Lemma lem52390 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term28 _5310 _5326 _5330 _5333 _5334 f p1) = (term29 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (@lem52389 _5330 _5333 _5334 (term20 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52391 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p2 : type1657 _5330 _5333 _5334) : (term30 _5310 _5326 _5330 _5333 _5334 f p1 p2) = ((term17 _5310 _5326 _5330 _5333 _5334 f p1 p2) = (term18 _5310 _5326 _5330 _5333 _5334 f p1 p2)).
Proof. exact (eq_refl (term30 _5310 _5326 _5330 _5333 _5334 f p1 p2)). Qed.
Lemma lem52392 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term31 _5310 _5326 _5330 _5333 _5334 f p1) = (term20 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (fun_ext (fun p2 : type1657 _5330 _5333 _5334 => @lem52391 _5310 _5326 _5330 _5333 _5334 f p1 p2)). Qed.
Lemma lem52393 {_5330 _5333 _5334 : Type'} : (@all (prod _5330 (prod _5334 _5333))) = (@all (prod _5330 (prod _5334 _5333))).
Proof. exact (eq_refl (@all (prod _5330 (prod _5334 _5333)))). Qed.
Lemma lem52394 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term28 _5310 _5326 _5330 _5333 _5334 f p1) = (term22 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (MK_COMB (@lem52393 _5330 _5333 _5334) (@lem52392 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem52396 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term32 _5310 _5326 _5330 _5333 _5334 f p1) = (term33 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (MK_COMB (@lem52395) (@lem52394 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52397 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p2 : prod _5334 _5333) : (term34 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2) = ((term35 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2) = (term36 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2)).
Proof. exact (eq_refl (term34 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2)). Qed.
Lemma lem52398 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term37 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term38 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (fun_ext (fun p2 : prod _5334 _5333 => @lem52397 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2)). Qed.
Lemma lem52399 {_5333 _5334 : Type'} : (@all (prod _5334 _5333)) = (@all (prod _5334 _5333)).
Proof. exact (eq_refl (@all (prod _5334 _5333))). Qed.
Lemma lem52400 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term39 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term40 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (MK_COMB (@lem52399 _5333 _5334) (@lem52398 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52401 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term41 _5310 _5326 _5330 _5333 _5334 f p1) = (term42 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (fun_ext (fun p1' : _5330 => @lem52400 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52402 {_5330 : Type'} : (@all _5330) = (@all _5330).
Proof. exact (eq_refl (@all _5330)). Qed.
Lemma lem52403 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term29 _5310 _5326 _5330 _5333 _5334 f p1) = (term43 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (MK_COMB (@lem52402 _5330) (@lem52401 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52404 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : ((term28 _5310 _5326 _5330 _5333 _5334 f p1) = (term29 _5310 _5326 _5330 _5333 _5334 f p1)) = ((term22 _5310 _5326 _5330 _5333 _5334 f p1) = (term43 _5310 _5326 _5330 _5333 _5334 f p1)).
Proof. exact (MK_COMB (@lem52396 _5310 _5326 _5330 _5333 _5334 f p1) (@lem52403 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52405 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term22 _5310 _5326 _5330 _5333 _5334 f p1) = (term43 _5310 _5326 _5330 _5333 _5334 f p1).
Proof. exact (EQ_MP (@lem52404 _5310 _5326 _5330 _5333 _5334 f p1) (@lem52390 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52417 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = (term5 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51887 _5106 _5107 P) (@lem51886 _5106 _5107 P)). Qed.
Lemma lem52418 {_5333 _5334 : Type'} (P : type1223 _5333 _5334) : (term4 _5333 _5334 P) = (term5 _5333 _5334 P).
Proof. exact (@lem52417 _5333 _5334 P). Qed.
Lemma lem52419 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term44 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term45 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (@lem52418 _5333 _5334 (term38 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52420 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p2 : prod _5334 _5333) : (term46 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2) = ((term35 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2) = (term36 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2)).
Proof. exact (eq_refl (term46 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2)). Qed.
Lemma lem52421 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term47 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term38 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (fun_ext (fun p2 : prod _5334 _5333 => @lem52420 _5310 _5326 _5330 _5333 _5334 f p1 p1' p2)). Qed.
Lemma lem52422 {_5333 _5334 : Type'} : (@all (prod _5334 _5333)) = (@all (prod _5334 _5333)).
Proof. exact (eq_refl (@all (prod _5334 _5333))). Qed.
Lemma lem52423 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term44 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term40 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (MK_COMB (@lem52422 _5333 _5334) (@lem52421 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem52425 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term48 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term49 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (MK_COMB (@lem52424) (@lem52423 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52426 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) (p2 : _5333) : (term50 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = ((term51 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)).
Proof. exact (eq_refl (term50 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52427 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) : (term53 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'') = (term54 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'').
Proof. exact (fun_ext (fun p2 : _5333 => @lem52426 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52428 {_5333 : Type'} : (@all _5333) = (@all _5333).
Proof. exact (eq_refl (@all _5333)). Qed.
Lemma lem52429 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) : (term55 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'') = (term56 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'').
Proof. exact (MK_COMB (@lem52428 _5333) (@lem52427 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'')). Qed.
Lemma lem52430 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term57 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term58 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (fun_ext (fun p1'' : _5334 => @lem52429 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'')). Qed.
Lemma lem52431 {_5334 : Type'} : (@all _5334) = (@all _5334).
Proof. exact (eq_refl (@all _5334)). Qed.
Lemma lem52432 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term45 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term59 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (MK_COMB (@lem52431 _5334) (@lem52430 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52433 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : ((term44 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term45 _5310 _5326 _5330 _5333 _5334 f p1 p1')) = ((term40 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term59 _5310 _5326 _5330 _5333 _5334 f p1 p1')).
Proof. exact (MK_COMB (@lem52425 _5310 _5326 _5330 _5333 _5334 f p1 p1') (@lem52432 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52434 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term40 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term59 _5310 _5326 _5330 _5333 _5334 f p1 p1').
Proof. exact (EQ_MP (@lem52433 _5310 _5326 _5330 _5333 _5334 f p1 p1') (@lem52419 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52451 {_5326 _5330 _5333 _5334 : Type'} (a0 : _5326) (a1 : type1657 _5330 _5333 _5334) : a0 = (term60 _5326 _5330 _5333 _5334 a0 a1).
Proof. exact (@lem51128 _5326 (type1657 _5330 _5333 _5334) a0 a1). Qed.
Lemma lem52452 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : w = (term61 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (@lem52451 _5326 _5330 _5333 _5334 w (term62 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52453 {_5326 _5330 _5333 _5334 : Type'} (a0 : _5326) (a1 : type1657 _5330 _5333 _5334) : a1 = (term63 _5326 _5330 _5333 _5334 a0 a1).
Proof. exact (@lem51159 _5326 (type1657 _5330 _5333 _5334) a0 a1). Qed.
Lemma lem52454 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term62 _5330 _5333 _5334 x y z) = (term64 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (@lem52453 _5326 _5330 _5333 _5334 w (term62 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52455 {_5326 : Type'} (w : _5326) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem52456 {_5326 : Type'} : (term65 _5326) = (term65 _5326).
Proof. exact (eq_refl (term65 _5326)). Qed.
Lemma lem52457 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term66 _5326 w) = (term67 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (MK_COMB (@lem52456 _5326) (@lem52452 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52458 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term67 _5326 _5330 _5333 _5334 w x y z) = (term61 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term67 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52459 {_5326 : Type'} (w : _5326) : (term68 _5326 w) = (term68 _5326 w).
Proof. exact (eq_refl (term68 _5326 w)). Qed.
Lemma lem52460 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term66 _5326 w) = (term67 _5326 _5330 _5333 _5334 w x y z)) = ((term66 _5326 w) = (term61 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52459 _5326 w) (@lem52458 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52461 {_5326 : Type'} (w : _5326) : (term66 _5326 w) = w.
Proof. exact (eq_refl (term66 _5326 w)). Qed.
Lemma lem52462 {_5326 : Type'} : (@eq _5326) = (@eq _5326).
Proof. exact (eq_refl (@eq _5326)). Qed.
Lemma lem52463 {_5326 : Type'} (w : _5326) : (term68 _5326 w) = (@eq _5326 w).
Proof. exact (MK_COMB (@lem52462 _5326) (@lem52461 _5326 w)). Qed.
Lemma lem52464 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term61 _5326 _5330 _5333 _5334 w x y z) = (term61 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term61 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52465 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term66 _5326 w) = (term61 _5326 _5330 _5333 _5334 w x y z)) = (w = (term61 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52463 _5326 w) (@lem52464 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52466 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term66 _5326 w) = (term67 _5326 _5330 _5333 _5334 w x y z)) = (w = (term61 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (TRANS (@lem52460 _5326 _5330 _5333 _5334 w x y z) (@lem52465 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52467 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : w = (term61 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52466 _5326 _5330 _5333 _5334 w x y z) (@lem52457 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52468 {_5326 : Type'} (w : _5326) : (@eq _5326 w) = (@eq _5326 w).
Proof. exact (eq_refl (@eq _5326 w)). Qed.
Lemma lem52469 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (w = w) = (w = (term61 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52468 _5326 w) (@lem52467 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52470 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : w = (term61 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52469 _5326 _5330 _5333 _5334 w x y z) (@lem52455 _5326 w)). Qed.
Lemma lem52471 {_5330 _5333 _5334 : Type'} (a0 : _5330) (a1 : prod _5334 _5333) : a0 = (term69 _5330 _5333 _5334 a0 a1).
Proof. exact (@lem51128 _5330 (prod _5334 _5333) a0 a1). Qed.
Lemma lem52472 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : x = (term70 _5330 _5333 _5334 x y z).
Proof. exact (@lem52471 _5330 _5333 _5334 x (@pair _5334 _5333 y z)). Qed.
Lemma lem52473 {_5330 _5333 _5334 : Type'} (a0 : _5330) (a1 : prod _5334 _5333) : a1 = (term71 _5330 _5333 _5334 a0 a1).
Proof. exact (@lem51159 _5330 (prod _5334 _5333) a0 a1). Qed.
Lemma lem52474 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (@pair _5334 _5333 y z) = (term72 _5330 _5333 _5334 x y z).
Proof. exact (@lem52473 _5330 _5333 _5334 x (@pair _5334 _5333 y z)). Qed.
Lemma lem52475 {_5330 : Type'} (x : _5330) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem52476 {_5330 : Type'} : (term65 _5330) = (term65 _5330).
Proof. exact (eq_refl (term65 _5330)). Qed.
Lemma lem52477 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term66 _5330 x) = (term73 _5330 _5333 _5334 x y z).
Proof. exact (MK_COMB (@lem52476 _5330) (@lem52472 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52478 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term73 _5330 _5333 _5334 x y z) = (term70 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term73 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52479 {_5330 : Type'} (x : _5330) : (term68 _5330 x) = (term68 _5330 x).
Proof. exact (eq_refl (term68 _5330 x)). Qed.
Lemma lem52480 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term66 _5330 x) = (term73 _5330 _5333 _5334 x y z)) = ((term66 _5330 x) = (term70 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52479 _5330 x) (@lem52478 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52481 {_5330 : Type'} (x : _5330) : (term66 _5330 x) = x.
Proof. exact (eq_refl (term66 _5330 x)). Qed.
Lemma lem52482 {_5330 : Type'} : (@eq _5330) = (@eq _5330).
Proof. exact (eq_refl (@eq _5330)). Qed.
Lemma lem52483 {_5330 : Type'} (x : _5330) : (term68 _5330 x) = (@eq _5330 x).
Proof. exact (MK_COMB (@lem52482 _5330) (@lem52481 _5330 x)). Qed.
Lemma lem52484 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term70 _5330 _5333 _5334 x y z) = (term70 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term70 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52485 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term66 _5330 x) = (term70 _5330 _5333 _5334 x y z)) = (x = (term70 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52483 _5330 x) (@lem52484 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52486 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term66 _5330 x) = (term73 _5330 _5333 _5334 x y z)) = (x = (term70 _5330 _5333 _5334 x y z)).
Proof. exact (TRANS (@lem52480 _5330 _5333 _5334 x y z) (@lem52485 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52487 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : x = (term70 _5330 _5333 _5334 x y z).
Proof. exact (EQ_MP (@lem52486 _5330 _5333 _5334 x y z) (@lem52477 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52488 {_5330 : Type'} (x : _5330) : (@eq _5330 x) = (@eq _5330 x).
Proof. exact (eq_refl (@eq _5330 x)). Qed.
Lemma lem52489 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (x = x) = (x = (term70 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52488 _5330 x) (@lem52487 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52490 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : x = (term70 _5330 _5333 _5334 x y z).
Proof. exact (EQ_MP (@lem52489 _5330 _5333 _5334 x y z) (@lem52475 _5330 x)). Qed.
Lemma lem52491 {_5333 _5334 : Type'} (a0 : _5334) (a1 : _5333) : a0 = (term74 _5333 _5334 a0 a1).
Proof. exact (@lem51128 _5334 _5333 a0 a1). Qed.
Lemma lem52492 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : y = (term74 _5333 _5334 y z).
Proof. exact (@lem52491 _5333 _5334 y z). Qed.
Lemma lem52493 {_5333 _5334 : Type'} (a0 : _5334) (a1 : _5333) : a1 = (term75 _5333 _5334 a0 a1).
Proof. exact (@lem51159 _5334 _5333 a0 a1). Qed.
Lemma lem52494 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : z = (term75 _5333 _5334 y z).
Proof. exact (@lem52493 _5333 _5334 y z). Qed.
Lemma lem52495 {_5334 : Type'} (y : _5334) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem52496 {_5334 : Type'} : (term65 _5334) = (term65 _5334).
Proof. exact (eq_refl (term65 _5334)). Qed.
Lemma lem52497 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term66 _5334 y) = (term76 _5333 _5334 y z).
Proof. exact (MK_COMB (@lem52496 _5334) (@lem52492 _5333 _5334 y z)). Qed.
Lemma lem52498 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term76 _5333 _5334 y z) = (term74 _5333 _5334 y z).
Proof. exact (eq_refl (term76 _5333 _5334 y z)). Qed.
Lemma lem52499 {_5334 : Type'} (y : _5334) : (term68 _5334 y) = (term68 _5334 y).
Proof. exact (eq_refl (term68 _5334 y)). Qed.
Lemma lem52500 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : ((term66 _5334 y) = (term76 _5333 _5334 y z)) = ((term66 _5334 y) = (term74 _5333 _5334 y z)).
Proof. exact (MK_COMB (@lem52499 _5334 y) (@lem52498 _5333 _5334 y z)). Qed.
Lemma lem52501 {_5334 : Type'} (y : _5334) : (term66 _5334 y) = y.
Proof. exact (eq_refl (term66 _5334 y)). Qed.
Lemma lem52502 {_5334 : Type'} : (@eq _5334) = (@eq _5334).
Proof. exact (eq_refl (@eq _5334)). Qed.
Lemma lem52503 {_5334 : Type'} (y : _5334) : (term68 _5334 y) = (@eq _5334 y).
Proof. exact (MK_COMB (@lem52502 _5334) (@lem52501 _5334 y)). Qed.
Lemma lem52504 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term74 _5333 _5334 y z) = (term74 _5333 _5334 y z).
Proof. exact (eq_refl (term74 _5333 _5334 y z)). Qed.
Lemma lem52505 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : ((term66 _5334 y) = (term74 _5333 _5334 y z)) = (y = (term74 _5333 _5334 y z)).
Proof. exact (MK_COMB (@lem52503 _5334 y) (@lem52504 _5333 _5334 y z)). Qed.
Lemma lem52506 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : ((term66 _5334 y) = (term76 _5333 _5334 y z)) = (y = (term74 _5333 _5334 y z)).
Proof. exact (TRANS (@lem52500 _5333 _5334 y z) (@lem52505 _5333 _5334 y z)). Qed.
Lemma lem52507 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : y = (term74 _5333 _5334 y z).
Proof. exact (EQ_MP (@lem52506 _5333 _5334 y z) (@lem52497 _5333 _5334 y z)). Qed.
Lemma lem52508 {_5334 : Type'} (y : _5334) : (@eq _5334 y) = (@eq _5334 y).
Proof. exact (eq_refl (@eq _5334 y)). Qed.
Lemma lem52509 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (y = y) = (y = (term74 _5333 _5334 y z)).
Proof. exact (MK_COMB (@lem52508 _5334 y) (@lem52507 _5333 _5334 y z)). Qed.
Lemma lem52510 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : y = (term74 _5333 _5334 y z).
Proof. exact (EQ_MP (@lem52509 _5333 _5334 y z) (@lem52495 _5334 y)). Qed.
Lemma lem52511 {_5333 : Type'} (z : _5333) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem52512 {_5333 : Type'} : (term65 _5333) = (term65 _5333).
Proof. exact (eq_refl (term65 _5333)). Qed.
Lemma lem52513 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term66 _5333 z) = (term77 _5333 _5334 y z).
Proof. exact (MK_COMB (@lem52512 _5333) (@lem52494 _5333 _5334 y z)). Qed.
Lemma lem52514 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term77 _5333 _5334 y z) = (term75 _5333 _5334 y z).
Proof. exact (eq_refl (term77 _5333 _5334 y z)). Qed.
Lemma lem52515 {_5333 : Type'} (z : _5333) : (term68 _5333 z) = (term68 _5333 z).
Proof. exact (eq_refl (term68 _5333 z)). Qed.
Lemma lem52516 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : ((term66 _5333 z) = (term77 _5333 _5334 y z)) = ((term66 _5333 z) = (term75 _5333 _5334 y z)).
Proof. exact (MK_COMB (@lem52515 _5333 z) (@lem52514 _5333 _5334 y z)). Qed.
Lemma lem52517 {_5333 : Type'} (z : _5333) : (term66 _5333 z) = z.
Proof. exact (eq_refl (term66 _5333 z)). Qed.
Lemma lem52518 {_5333 : Type'} : (@eq _5333) = (@eq _5333).
Proof. exact (eq_refl (@eq _5333)). Qed.
Lemma lem52519 {_5333 : Type'} (z : _5333) : (term68 _5333 z) = (@eq _5333 z).
Proof. exact (MK_COMB (@lem52518 _5333) (@lem52517 _5333 z)). Qed.
Lemma lem52520 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term75 _5333 _5334 y z) = (term75 _5333 _5334 y z).
Proof. exact (eq_refl (term75 _5333 _5334 y z)). Qed.
Lemma lem52521 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : ((term66 _5333 z) = (term75 _5333 _5334 y z)) = (z = (term75 _5333 _5334 y z)).
Proof. exact (MK_COMB (@lem52519 _5333 z) (@lem52520 _5333 _5334 y z)). Qed.
Lemma lem52522 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : ((term66 _5333 z) = (term77 _5333 _5334 y z)) = (z = (term75 _5333 _5334 y z)).
Proof. exact (TRANS (@lem52516 _5333 _5334 y z) (@lem52521 _5333 _5334 y z)). Qed.
Lemma lem52523 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : z = (term75 _5333 _5334 y z).
Proof. exact (EQ_MP (@lem52522 _5333 _5334 y z) (@lem52513 _5333 _5334 y z)). Qed.
Lemma lem52524 {_5333 : Type'} (z : _5333) : (@eq _5333 z) = (@eq _5333 z).
Proof. exact (eq_refl (@eq _5333 z)). Qed.
Lemma lem52525 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (z = z) = (z = (term75 _5333 _5334 y z)).
Proof. exact (MK_COMB (@lem52524 _5333 z) (@lem52523 _5333 _5334 y z)). Qed.
Lemma lem52526 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : z = (term75 _5333 _5334 y z).
Proof. exact (EQ_MP (@lem52525 _5333 _5334 y z) (@lem52511 _5333 z)). Qed.
Lemma lem52527 {_5333 _5334 : Type'} : (term78 _5333 _5334) = (term78 _5333 _5334).
Proof. exact (eq_refl (term78 _5333 _5334)). Qed.
Lemma lem52528 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term79 _5333 _5334 y z) = (term80 _5330 _5333 _5334 x y z).
Proof. exact (MK_COMB (@lem52527 _5333 _5334) (@lem52474 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52529 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term80 _5330 _5333 _5334 x y z) = (term81 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term80 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52530 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term82 _5333 _5334 y z) = (term82 _5333 _5334 y z).
Proof. exact (eq_refl (term82 _5333 _5334 y z)). Qed.
Lemma lem52531 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term79 _5333 _5334 y z) = (term80 _5330 _5333 _5334 x y z)) = ((term79 _5333 _5334 y z) = (term81 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52530 _5333 _5334 y z) (@lem52529 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52532 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term79 _5333 _5334 y z) = (term74 _5333 _5334 y z).
Proof. exact (eq_refl (term79 _5333 _5334 y z)). Qed.
Lemma lem52533 {_5334 : Type'} : (@eq _5334) = (@eq _5334).
Proof. exact (eq_refl (@eq _5334)). Qed.
Lemma lem52534 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term82 _5333 _5334 y z) = (term83 _5333 _5334 y z).
Proof. exact (MK_COMB (@lem52533 _5334) (@lem52532 _5333 _5334 y z)). Qed.
Lemma lem52535 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term81 _5330 _5333 _5334 x y z) = (term81 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term81 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52536 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term79 _5333 _5334 y z) = (term81 _5330 _5333 _5334 x y z)) = ((term74 _5333 _5334 y z) = (term81 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52534 _5333 _5334 y z) (@lem52535 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52537 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term79 _5333 _5334 y z) = (term80 _5330 _5333 _5334 x y z)) = ((term74 _5333 _5334 y z) = (term81 _5330 _5333 _5334 x y z)).
Proof. exact (TRANS (@lem52531 _5330 _5333 _5334 x y z) (@lem52536 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52538 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term74 _5333 _5334 y z) = (term81 _5330 _5333 _5334 x y z).
Proof. exact (EQ_MP (@lem52537 _5330 _5333 _5334 x y z) (@lem52528 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52539 {_5334 : Type'} (y : _5334) : (@eq _5334 y) = (@eq _5334 y).
Proof. exact (eq_refl (@eq _5334 y)). Qed.
Lemma lem52540 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (y = (term74 _5333 _5334 y z)) = (y = (term81 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52539 _5334 y) (@lem52538 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52541 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : y = (term81 _5330 _5333 _5334 x y z).
Proof. exact (EQ_MP (@lem52540 _5330 _5333 _5334 x y z) (@lem52510 _5333 _5334 y z)). Qed.
Lemma lem52542 {_5333 _5334 : Type'} : (term84 _5333 _5334) = (term84 _5333 _5334).
Proof. exact (eq_refl (term84 _5333 _5334)). Qed.
Lemma lem52543 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term85 _5333 _5334 y z) = (term86 _5330 _5333 _5334 x y z).
Proof. exact (MK_COMB (@lem52542 _5333 _5334) (@lem52474 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52544 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term86 _5330 _5333 _5334 x y z) = (term87 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term86 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52545 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term88 _5333 _5334 y z) = (term88 _5333 _5334 y z).
Proof. exact (eq_refl (term88 _5333 _5334 y z)). Qed.
Lemma lem52546 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term85 _5333 _5334 y z) = (term86 _5330 _5333 _5334 x y z)) = ((term85 _5333 _5334 y z) = (term87 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52545 _5333 _5334 y z) (@lem52544 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52547 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term85 _5333 _5334 y z) = (term75 _5333 _5334 y z).
Proof. exact (eq_refl (term85 _5333 _5334 y z)). Qed.
Lemma lem52548 {_5333 : Type'} : (@eq _5333) = (@eq _5333).
Proof. exact (eq_refl (@eq _5333)). Qed.
Lemma lem52549 {_5333 _5334 : Type'} (y : _5334) (z : _5333) : (term88 _5333 _5334 y z) = (term89 _5333 _5334 y z).
Proof. exact (MK_COMB (@lem52548 _5333) (@lem52547 _5333 _5334 y z)). Qed.
Lemma lem52550 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term87 _5330 _5333 _5334 x y z) = (term87 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term87 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52551 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term85 _5333 _5334 y z) = (term87 _5330 _5333 _5334 x y z)) = ((term75 _5333 _5334 y z) = (term87 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52549 _5333 _5334 y z) (@lem52550 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52552 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : ((term85 _5333 _5334 y z) = (term86 _5330 _5333 _5334 x y z)) = ((term75 _5333 _5334 y z) = (term87 _5330 _5333 _5334 x y z)).
Proof. exact (TRANS (@lem52546 _5330 _5333 _5334 x y z) (@lem52551 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52553 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term75 _5333 _5334 y z) = (term87 _5330 _5333 _5334 x y z).
Proof. exact (EQ_MP (@lem52552 _5330 _5333 _5334 x y z) (@lem52543 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52554 {_5333 : Type'} (z : _5333) : (@eq _5333 z) = (@eq _5333 z).
Proof. exact (eq_refl (@eq _5333 z)). Qed.
Lemma lem52555 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (z = (term75 _5333 _5334 y z)) = (z = (term87 _5330 _5333 _5334 x y z)).
Proof. exact (MK_COMB (@lem52554 _5333 z) (@lem52553 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52556 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : z = (term87 _5330 _5333 _5334 x y z).
Proof. exact (EQ_MP (@lem52555 _5330 _5333 _5334 x y z) (@lem52526 _5333 _5334 y z)). Qed.
Lemma lem52557 {_5330 _5333 _5334 : Type'} : (term90 _5330 _5333 _5334) = (term90 _5330 _5333 _5334).
Proof. exact (eq_refl (term90 _5330 _5333 _5334)). Qed.
Lemma lem52558 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term91 _5330 _5333 _5334 x y z) = (term92 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (MK_COMB (@lem52557 _5330 _5333 _5334) (@lem52454 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52559 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term92 _5326 _5330 _5333 _5334 w x y z) = (term93 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term92 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52560 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term94 _5330 _5333 _5334 x y z) = (term94 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term94 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52561 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term91 _5330 _5333 _5334 x y z) = (term92 _5326 _5330 _5333 _5334 w x y z)) = ((term91 _5330 _5333 _5334 x y z) = (term93 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52560 _5330 _5333 _5334 x y z) (@lem52559 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52562 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term91 _5330 _5333 _5334 x y z) = (term70 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term91 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52563 {_5330 : Type'} : (@eq _5330) = (@eq _5330).
Proof. exact (eq_refl (@eq _5330)). Qed.
Lemma lem52564 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term94 _5330 _5333 _5334 x y z) = (term95 _5330 _5333 _5334 x y z).
Proof. exact (MK_COMB (@lem52563 _5330) (@lem52562 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52565 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term93 _5326 _5330 _5333 _5334 w x y z) = (term93 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term93 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52566 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term91 _5330 _5333 _5334 x y z) = (term93 _5326 _5330 _5333 _5334 w x y z)) = ((term70 _5330 _5333 _5334 x y z) = (term93 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52564 _5330 _5333 _5334 x y z) (@lem52565 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52567 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term91 _5330 _5333 _5334 x y z) = (term92 _5326 _5330 _5333 _5334 w x y z)) = ((term70 _5330 _5333 _5334 x y z) = (term93 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (TRANS (@lem52561 _5326 _5330 _5333 _5334 w x y z) (@lem52566 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52568 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term70 _5330 _5333 _5334 x y z) = (term93 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52567 _5326 _5330 _5333 _5334 w x y z) (@lem52558 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52569 {_5330 : Type'} (x : _5330) : (@eq _5330 x) = (@eq _5330 x).
Proof. exact (eq_refl (@eq _5330 x)). Qed.
Lemma lem52570 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (x = (term70 _5330 _5333 _5334 x y z)) = (x = (term93 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52569 _5330 x) (@lem52568 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52571 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : x = (term93 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52570 _5326 _5330 _5333 _5334 w x y z) (@lem52490 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52572 {_5330 _5333 _5334 : Type'} : (term96 _5330 _5333 _5334) = (term96 _5330 _5333 _5334).
Proof. exact (eq_refl (term96 _5330 _5333 _5334)). Qed.
Lemma lem52573 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term97 _5330 _5333 _5334 x y z) = (term98 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (MK_COMB (@lem52572 _5330 _5333 _5334) (@lem52454 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52574 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term98 _5326 _5330 _5333 _5334 w x y z) = (term99 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term98 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52575 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term100 _5330 _5333 _5334 x y z) = (term100 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term100 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52576 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term97 _5330 _5333 _5334 x y z) = (term98 _5326 _5330 _5333 _5334 w x y z)) = ((term97 _5330 _5333 _5334 x y z) = (term99 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52575 _5330 _5333 _5334 x y z) (@lem52574 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52577 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term97 _5330 _5333 _5334 x y z) = (term81 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term97 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52578 {_5334 : Type'} : (@eq _5334) = (@eq _5334).
Proof. exact (eq_refl (@eq _5334)). Qed.
Lemma lem52579 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term100 _5330 _5333 _5334 x y z) = (term101 _5330 _5333 _5334 x y z).
Proof. exact (MK_COMB (@lem52578 _5334) (@lem52577 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52580 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term99 _5326 _5330 _5333 _5334 w x y z) = (term99 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term99 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52581 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term97 _5330 _5333 _5334 x y z) = (term99 _5326 _5330 _5333 _5334 w x y z)) = ((term81 _5330 _5333 _5334 x y z) = (term99 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52579 _5330 _5333 _5334 x y z) (@lem52580 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52582 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term97 _5330 _5333 _5334 x y z) = (term98 _5326 _5330 _5333 _5334 w x y z)) = ((term81 _5330 _5333 _5334 x y z) = (term99 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (TRANS (@lem52576 _5326 _5330 _5333 _5334 w x y z) (@lem52581 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52583 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term81 _5330 _5333 _5334 x y z) = (term99 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52582 _5326 _5330 _5333 _5334 w x y z) (@lem52573 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52584 {_5334 : Type'} (y : _5334) : (@eq _5334 y) = (@eq _5334 y).
Proof. exact (eq_refl (@eq _5334 y)). Qed.
Lemma lem52585 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (y = (term81 _5330 _5333 _5334 x y z)) = (y = (term99 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52584 _5334 y) (@lem52583 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52586 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : y = (term99 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52585 _5326 _5330 _5333 _5334 w x y z) (@lem52541 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52587 {_5330 _5333 _5334 : Type'} : (term102 _5330 _5333 _5334) = (term102 _5330 _5333 _5334).
Proof. exact (eq_refl (term102 _5330 _5333 _5334)). Qed.
Lemma lem52588 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term103 _5330 _5333 _5334 x y z) = (term104 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (MK_COMB (@lem52587 _5330 _5333 _5334) (@lem52454 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52589 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term104 _5326 _5330 _5333 _5334 w x y z) = (term105 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term104 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52590 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term106 _5330 _5333 _5334 x y z) = (term106 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term106 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52591 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term103 _5330 _5333 _5334 x y z) = (term104 _5326 _5330 _5333 _5334 w x y z)) = ((term103 _5330 _5333 _5334 x y z) = (term105 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52590 _5330 _5333 _5334 x y z) (@lem52589 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52592 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term103 _5330 _5333 _5334 x y z) = (term87 _5330 _5333 _5334 x y z).
Proof. exact (eq_refl (term103 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52593 {_5333 : Type'} : (@eq _5333) = (@eq _5333).
Proof. exact (eq_refl (@eq _5333)). Qed.
Lemma lem52594 {_5330 _5333 _5334 : Type'} (x : _5330) (y : _5334) (z : _5333) : (term106 _5330 _5333 _5334 x y z) = (term107 _5330 _5333 _5334 x y z).
Proof. exact (MK_COMB (@lem52593 _5333) (@lem52592 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52595 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term105 _5326 _5330 _5333 _5334 w x y z) = (term105 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (eq_refl (term105 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52596 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term103 _5330 _5333 _5334 x y z) = (term105 _5326 _5330 _5333 _5334 w x y z)) = ((term87 _5330 _5333 _5334 x y z) = (term105 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52594 _5330 _5333 _5334 x y z) (@lem52595 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52597 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term103 _5330 _5333 _5334 x y z) = (term104 _5326 _5330 _5333 _5334 w x y z)) = ((term87 _5330 _5333 _5334 x y z) = (term105 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (TRANS (@lem52591 _5326 _5330 _5333 _5334 w x y z) (@lem52596 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52598 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term87 _5330 _5333 _5334 x y z) = (term105 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52597 _5326 _5330 _5333 _5334 w x y z) (@lem52588 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52599 {_5333 : Type'} (z : _5333) : (@eq _5333 z) = (@eq _5333 z).
Proof. exact (eq_refl (@eq _5333 z)). Qed.
Lemma lem52600 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (z = (term87 _5330 _5333 _5334 x y z)) = (z = (term105 _5326 _5330 _5333 _5334 w x y z)).
Proof. exact (MK_COMB (@lem52599 _5333 z) (@lem52598 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52601 {_5326 _5330 _5333 _5334 : Type'} (w : _5326) (x : _5330) (y : _5334) (z : _5333) : z = (term105 _5326 _5330 _5333 _5334 w x y z).
Proof. exact (EQ_MP (@lem52600 _5326 _5330 _5333 _5334 w x y z) (@lem52556 _5330 _5333 _5334 x y z)). Qed.
Lemma lem52602 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term108 _5310 _5326 _5330 _5333 _5334 f) = (term108 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (eq_refl (term108 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52603 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term109 _5310 _5326 _5330 _5333 _5334 f w) = (term110 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (MK_COMB (@lem52602 _5310 _5326 _5330 _5333 _5334 f) (@lem52470 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52604 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term110 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term111 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term110 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52605 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : (term112 _5310 _5326 _5330 _5333 _5334 f w) = (term112 _5310 _5326 _5330 _5333 _5334 f w).
Proof. exact (eq_refl (term112 _5310 _5326 _5330 _5333 _5334 f w)). Qed.
Lemma lem52606 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term109 _5310 _5326 _5330 _5333 _5334 f w) = (term110 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term109 _5310 _5326 _5330 _5333 _5334 f w) = (term111 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52605 _5310 _5326 _5330 _5333 _5334 f w) (@lem52604 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52607 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : (term109 _5310 _5326 _5330 _5333 _5334 f w) = (term113 _5310 _5326 _5330 _5333 _5334 f w).
Proof. exact (eq_refl (term109 _5310 _5326 _5330 _5333 _5334 f w)). Qed.
Lemma lem52608 {_5310 _5330 _5333 _5334 : Type'} : (@eq (_5330 -> _5334 -> _5333 -> _5310)) = (@eq (_5330 -> _5334 -> _5333 -> _5310)).
Proof. exact (eq_refl (@eq (_5330 -> _5334 -> _5333 -> _5310))). Qed.
Lemma lem52609 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : (term112 _5310 _5326 _5330 _5333 _5334 f w) = (term114 _5310 _5326 _5330 _5333 _5334 f w).
Proof. exact (MK_COMB (@lem52608 _5310 _5330 _5333 _5334) (@lem52607 _5310 _5326 _5330 _5333 _5334 f w)). Qed.
Lemma lem52610 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term111 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term111 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term111 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52611 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term109 _5310 _5326 _5330 _5333 _5334 f w) = (term111 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term113 _5310 _5326 _5330 _5333 _5334 f w) = (term111 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52609 _5310 _5326 _5330 _5333 _5334 f w) (@lem52610 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52612 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term109 _5310 _5326 _5330 _5333 _5334 f w) = (term110 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term113 _5310 _5326 _5330 _5333 _5334 f w) = (term111 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (TRANS (@lem52606 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52611 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52613 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term113 _5310 _5326 _5330 _5333 _5334 f w) = (term111 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (EQ_MP (@lem52612 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52603 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52614 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term115 _5310 _5326 _5330 _5333 _5334 f w x) = (term116 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (MK_COMB (@lem52613 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52571 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52615 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term116 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term117 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term116 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52616 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : (term118 _5310 _5326 _5330 _5333 _5334 f w x) = (term118 _5310 _5326 _5330 _5333 _5334 f w x).
Proof. exact (eq_refl (term118 _5310 _5326 _5330 _5333 _5334 f w x)). Qed.
Lemma lem52617 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term115 _5310 _5326 _5330 _5333 _5334 f w x) = (term116 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term115 _5310 _5326 _5330 _5333 _5334 f w x) = (term117 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52616 _5310 _5326 _5330 _5333 _5334 f w x) (@lem52615 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52618 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : (term115 _5310 _5326 _5330 _5333 _5334 f w x) = (term119 _5310 _5326 _5330 _5333 _5334 f w x).
Proof. exact (eq_refl (term115 _5310 _5326 _5330 _5333 _5334 f w x)). Qed.
Lemma lem52619 {_5310 _5333 _5334 : Type'} : (@eq (_5334 -> _5333 -> _5310)) = (@eq (_5334 -> _5333 -> _5310)).
Proof. exact (eq_refl (@eq (_5334 -> _5333 -> _5310))). Qed.
Lemma lem52620 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : (term118 _5310 _5326 _5330 _5333 _5334 f w x) = (term120 _5310 _5326 _5330 _5333 _5334 f w x).
Proof. exact (MK_COMB (@lem52619 _5310 _5333 _5334) (@lem52618 _5310 _5326 _5330 _5333 _5334 f w x)). Qed.
Lemma lem52621 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term117 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term117 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term117 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52622 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term115 _5310 _5326 _5330 _5333 _5334 f w x) = (term117 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term119 _5310 _5326 _5330 _5333 _5334 f w x) = (term117 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52620 _5310 _5326 _5330 _5333 _5334 f w x) (@lem52621 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52623 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term115 _5310 _5326 _5330 _5333 _5334 f w x) = (term116 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term119 _5310 _5326 _5330 _5333 _5334 f w x) = (term117 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (TRANS (@lem52617 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52622 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52624 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term119 _5310 _5326 _5330 _5333 _5334 f w x) = (term117 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (EQ_MP (@lem52623 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52614 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52625 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term121 _5310 _5326 _5330 _5333 _5334 f w x y) = (term122 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (MK_COMB (@lem52624 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52586 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52626 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term122 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term123 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term122 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52627 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : (term124 _5310 _5326 _5330 _5333 _5334 f w x y) = (term124 _5310 _5326 _5330 _5333 _5334 f w x y).
Proof. exact (eq_refl (term124 _5310 _5326 _5330 _5333 _5334 f w x y)). Qed.
Lemma lem52628 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term121 _5310 _5326 _5330 _5333 _5334 f w x y) = (term122 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term121 _5310 _5326 _5330 _5333 _5334 f w x y) = (term123 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52627 _5310 _5326 _5330 _5333 _5334 f w x y) (@lem52626 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52629 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : (term121 _5310 _5326 _5330 _5333 _5334 f w x y) = (term125 _5310 _5326 _5330 _5333 _5334 f w x y).
Proof. exact (eq_refl (term121 _5310 _5326 _5330 _5333 _5334 f w x y)). Qed.
Lemma lem52630 {_5310 _5333 : Type'} : (@eq (_5333 -> _5310)) = (@eq (_5333 -> _5310)).
Proof. exact (eq_refl (@eq (_5333 -> _5310))). Qed.
Lemma lem52631 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : (term124 _5310 _5326 _5330 _5333 _5334 f w x y) = (term126 _5310 _5326 _5330 _5333 _5334 f w x y).
Proof. exact (MK_COMB (@lem52630 _5310 _5333) (@lem52629 _5310 _5326 _5330 _5333 _5334 f w x y)). Qed.
Lemma lem52632 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term123 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term123 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term123 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52633 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term121 _5310 _5326 _5330 _5333 _5334 f w x y) = (term123 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term125 _5310 _5326 _5330 _5333 _5334 f w x y) = (term123 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52631 _5310 _5326 _5330 _5333 _5334 f w x y) (@lem52632 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52634 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term121 _5310 _5326 _5330 _5333 _5334 f w x y) = (term122 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term125 _5310 _5326 _5330 _5333 _5334 f w x y) = (term123 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (TRANS (@lem52628 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52633 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52635 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term125 _5310 _5326 _5330 _5333 _5334 f w x y) = (term123 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (EQ_MP (@lem52634 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52625 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52636 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term127 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term128 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (MK_COMB (@lem52635 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52601 _5326 _5330 _5333 _5334 w x y z)). Qed.
Lemma lem52637 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term128 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term128 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52638 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term130 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term130 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term130 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52639 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term127 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term128 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term127 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52638 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52637 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52640 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term127 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term52 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term127 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52641 {_5310 : Type'} : (@eq _5310) = (@eq _5310).
Proof. exact (eq_refl (@eq _5310)). Qed.
Lemma lem52642 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term130 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term131 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (MK_COMB (@lem52641 _5310) (@lem52640 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52643 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term129 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term129 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52644 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term127 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term52 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (MK_COMB (@lem52642 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52643 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52645 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term127 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term128 _5310 _5326 _5330 _5333 _5334 f w x y z)) = ((term52 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (TRANS (@lem52639 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52644 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52646 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term52 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (EQ_MP (@lem52645 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52636 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52647 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term129 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term52 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (SYM (@lem52646 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52648 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term132 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term129 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term132 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52649 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term132 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term52 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (TRANS (@lem52648 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52647 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52650 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : term133 _5310 _5326 _5330 _5333 _5334 f w x y.
Proof. exact (fun z : _5333 => @lem52649 _5310 _5326 _5330 _5333 _5334 f w x y z). Qed.
Lemma lem52651 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : term134 _5310 _5326 _5330 _5333 _5334 f w x.
Proof. exact (fun y : _5334 => @lem52650 _5310 _5326 _5330 _5333 _5334 f w x y). Qed.
Lemma lem52652 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : term135 _5310 _5326 _5330 _5333 _5334 f w.
Proof. exact (fun x : _5330 => @lem52651 _5310 _5326 _5330 _5333 _5334 f w x). Qed.
Lemma lem52653 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : term136 _5310 _5326 _5330 _5333 _5334 f.
Proof. exact (fun w : _5326 => @lem52652 _5310 _5326 _5330 _5333 _5334 f w). Qed.
Lemma lem52654 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : term137 _5310 _5326 _5330 _5333 _5334 f.
Proof. exact (ex_intro (term138 _5310 _5326 _5330 _5333 _5334 f) (term139 _5310 _5326 _5330 _5333 _5334 f) (@lem52653 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52656 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem52657 {_5310 : Type'} (a : _5310) (b : _5310) : (a = b) = (@GEQ _5310 a b).
Proof. exact (@lem52656 _5310 a b). Qed.
Lemma lem52658 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : ((term52 _5310 _5326 _5330 _5333 _5334 _1488 w x y z) = (term52 _5310 _5326 _5330 _5333 _5334 f w x y z)) = (term140 _5310 _5326 _5330 _5333 _5334 _1488 f w x y z).
Proof. exact (@lem52657 _5310 (term52 _5310 _5326 _5330 _5333 _5334 _1488 w x y z) (term52 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52659 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : (term141 _5310 _5326 _5330 _5333 _5334 _1488 f w x y) = (term142 _5310 _5326 _5330 _5333 _5334 _1488 f w x y).
Proof. exact (fun_ext (fun z : _5333 => @lem52658 _5310 _5326 _5330 _5333 _5334 _1488 f w x y z)). Qed.
Lemma lem52660 {_5333 : Type'} : (@all _5333) = (@all _5333).
Proof. exact (eq_refl (@all _5333)). Qed.
Lemma lem52661 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : (term143 _5310 _5326 _5330 _5333 _5334 _1488 f w x y) = (term144 _5310 _5326 _5330 _5333 _5334 _1488 f w x y).
Proof. exact (MK_COMB (@lem52660 _5333) (@lem52659 _5310 _5326 _5330 _5333 _5334 _1488 f w x y)). Qed.
Lemma lem52662 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : (term145 _5310 _5326 _5330 _5333 _5334 _1488 f w x) = (term146 _5310 _5326 _5330 _5333 _5334 _1488 f w x).
Proof. exact (fun_ext (fun y : _5334 => @lem52661 _5310 _5326 _5330 _5333 _5334 _1488 f w x y)). Qed.
Lemma lem52663 {_5334 : Type'} : (@all _5334) = (@all _5334).
Proof. exact (eq_refl (@all _5334)). Qed.
Lemma lem52664 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : (term147 _5310 _5326 _5330 _5333 _5334 _1488 f w x) = (term148 _5310 _5326 _5330 _5333 _5334 _1488 f w x).
Proof. exact (MK_COMB (@lem52663 _5334) (@lem52662 _5310 _5326 _5330 _5333 _5334 _1488 f w x)). Qed.
Lemma lem52665 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : (term149 _5310 _5326 _5330 _5333 _5334 _1488 f w) = (term150 _5310 _5326 _5330 _5333 _5334 _1488 f w).
Proof. exact (fun_ext (fun x : _5330 => @lem52664 _5310 _5326 _5330 _5333 _5334 _1488 f w x)). Qed.
Lemma lem52666 {_5330 : Type'} : (@all _5330) = (@all _5330).
Proof. exact (eq_refl (@all _5330)). Qed.
Lemma lem52667 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : (term151 _5310 _5326 _5330 _5333 _5334 _1488 f w) = (term152 _5310 _5326 _5330 _5333 _5334 _1488 f w).
Proof. exact (MK_COMB (@lem52666 _5330) (@lem52665 _5310 _5326 _5330 _5333 _5334 _1488 f w)). Qed.
Lemma lem52668 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term153 _5310 _5326 _5330 _5333 _5334 _1488 f) = (term154 _5310 _5326 _5330 _5333 _5334 _1488 f).
Proof. exact (fun_ext (fun w : _5326 => @lem52667 _5310 _5326 _5330 _5333 _5334 _1488 f w)). Qed.
Lemma lem52669 {_5326 : Type'} : (@all _5326) = (@all _5326).
Proof. exact (eq_refl (@all _5326)). Qed.
Lemma lem52670 {_5310 _5326 _5330 _5333 _5334 : Type'} (_1488 : type1218 _5310 _5326 _5330 _5333 _5334) (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term155 _5310 _5326 _5330 _5333 _5334 _1488 f) = (term156 _5310 _5326 _5330 _5333 _5334 _1488 f).
Proof. exact (MK_COMB (@lem52669 _5326) (@lem52668 _5310 _5326 _5330 _5333 _5334 _1488 f)). Qed.
Lemma lem52671 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term138 _5310 _5326 _5330 _5333 _5334 f) = (term157 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (fun_ext (fun _1488 : type1218 _5310 _5326 _5330 _5333 _5334 => @lem52670 _5310 _5326 _5330 _5333 _5334 _1488 f)). Qed.
Lemma lem52672 {_5310 _5326 _5330 _5333 _5334 : Type'} : (@ex ((prod _5326 (prod _5330 (prod _5334 _5333))) -> _5310)) = (@ex ((prod _5326 (prod _5330 (prod _5334 _5333))) -> _5310)).
Proof. exact (eq_refl (@ex ((prod _5326 (prod _5330 (prod _5334 _5333))) -> _5310))). Qed.
Lemma lem52673 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term137 _5310 _5326 _5330 _5333 _5334 f) = (term158 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (MK_COMB (@lem52672 _5310 _5326 _5330 _5333 _5334) (@lem52671 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52674 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : term158 _5310 _5326 _5330 _5333 _5334 f.
Proof. exact (EQ_MP (@lem52673 _5310 _5326 _5330 _5333 _5334 f) (@lem52654 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52676 {_5076 : Type'} (P : _5076 -> Prop) : term159 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem52677 {_5310 _5326 _5330 _5333 _5334 : Type'} (P : type327 _5310 _5326 _5330 _5333 _5334) : term160 _5310 _5326 _5330 _5333 _5334 P.
Proof. exact (@lem52676 (type1218 _5310 _5326 _5330 _5333 _5334) P). Qed.
Lemma lem52678 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : term161 _5310 _5326 _5330 _5333 _5334 f.
Proof. exact (@lem52677 _5310 _5326 _5330 _5333 _5334 (term157 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52679 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : term162 _5310 _5326 _5330 _5333 _5334 f.
Proof. exact (@lem52678 _5310 _5326 _5330 _5333 _5334 f (@lem52674 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52680 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term162 _5310 _5326 _5330 _5333 _5334 f) = (term163 _5310 _5326 _5330 _5333 _5334 f).
Proof. exact (eq_refl (term162 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52681 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : term163 _5310 _5326 _5330 _5333 _5334 f.
Proof. exact (EQ_MP (@lem52680 _5310 _5326 _5330 _5333 _5334 f) (@lem52679 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52682 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : term164 _5310 _5326 _5330 _5333 _5334 f w.
Proof. exact (@lem52681 _5310 _5326 _5330 _5333 _5334 f w). Qed.
Lemma lem52683 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : (term164 _5310 _5326 _5330 _5333 _5334 f w) = (term165 _5310 _5326 _5330 _5333 _5334 f w).
Proof. exact (eq_refl (term164 _5310 _5326 _5330 _5333 _5334 f w)). Qed.
Lemma lem52684 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) : term165 _5310 _5326 _5330 _5333 _5334 f w.
Proof. exact (EQ_MP (@lem52683 _5310 _5326 _5330 _5333 _5334 f w) (@lem52682 _5310 _5326 _5330 _5333 _5334 f w)). Qed.
Lemma lem52685 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : term166 _5310 _5326 _5330 _5333 _5334 f w x.
Proof. exact (@lem52684 _5310 _5326 _5330 _5333 _5334 f w x). Qed.
Lemma lem52686 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : (term166 _5310 _5326 _5330 _5333 _5334 f w x) = (term167 _5310 _5326 _5330 _5333 _5334 f w x).
Proof. exact (eq_refl (term166 _5310 _5326 _5330 _5333 _5334 f w x)). Qed.
Lemma lem52687 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) : term167 _5310 _5326 _5330 _5333 _5334 f w x.
Proof. exact (EQ_MP (@lem52686 _5310 _5326 _5330 _5333 _5334 f w x) (@lem52685 _5310 _5326 _5330 _5333 _5334 f w x)). Qed.
Lemma lem52688 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : term168 _5310 _5326 _5330 _5333 _5334 f w x y.
Proof. exact (@lem52687 _5310 _5326 _5330 _5333 _5334 f w x y). Qed.
Lemma lem52689 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : (term168 _5310 _5326 _5330 _5333 _5334 f w x y) = (term169 _5310 _5326 _5330 _5333 _5334 f w x y).
Proof. exact (eq_refl (term168 _5310 _5326 _5330 _5333 _5334 f w x y)). Qed.
Lemma lem52690 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) : term169 _5310 _5326 _5330 _5333 _5334 f w x y.
Proof. exact (EQ_MP (@lem52689 _5310 _5326 _5330 _5333 _5334 f w x y) (@lem52688 _5310 _5326 _5330 _5333 _5334 f w x y)). Qed.
Lemma lem52691 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : term170 _5310 _5326 _5330 _5333 _5334 f w x y z.
Proof. exact (@lem52690 _5310 _5326 _5330 _5333 _5334 f w x y z). Qed.
Lemma lem52692 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term170 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term171 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (eq_refl (term170 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52693 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : term171 _5310 _5326 _5330 _5333 _5334 f w x y z.
Proof. exact (EQ_MP (@lem52692 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52691 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52695 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem52696 {_5310 : Type'} (a : _5310) (b : _5310) : (@GEQ _5310 a b) = (a = b).
Proof. exact (@lem52695 _5310 a b). Qed.
Lemma lem52697 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term171 _5310 _5326 _5330 _5333 _5334 f w x y z) = ((term51 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term52 _5310 _5326 _5330 _5333 _5334 f w x y z)).
Proof. exact (@lem52696 _5310 (term51 _5310 _5326 _5330 _5333 _5334 f w x y z) (term52 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52698 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term51 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term52 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (EQ_MP (@lem52697 _5310 _5326 _5330 _5333 _5334 f w x y z) (@lem52693 _5310 _5326 _5330 _5333 _5334 f w x y z)). Qed.
Lemma lem52699 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (w : _5326) (x : _5330) (y : _5334) (z : _5333) : (term51 _5310 _5326 _5330 _5333 _5334 f w x y z) = (term52 _5310 _5326 _5330 _5333 _5334 f w x y z).
Proof. exact (@lem52698 _5310 _5326 _5330 _5333 _5334 f w x y z). Qed.
Lemma lem52700 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) (p2 : _5333) : (term51 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2).
Proof. exact (@lem52699 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2). Qed.
Lemma lem52701 {_5310 : Type'} : (@eq _5310) = (@eq _5310).
Proof. exact (eq_refl (@eq _5310)). Qed.
Lemma lem52702 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) (p2 : _5333) : (term172 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term131 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2).
Proof. exact (MK_COMB (@lem52701 _5310) (@lem52700 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52703 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) (p2 : _5333) : (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2).
Proof. exact (eq_refl (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52704 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) (p2 : _5333) : ((term51 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)) = ((term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)).
Proof. exact (MK_COMB (@lem52702 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) (@lem52703 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52706 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem52707 {_5310 : Type'} (x : _5310) : (x = x) = True.
Proof. exact (@lem52706 _5310 x). Qed.
Lemma lem52708 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) (p2 : _5333) : ((term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)) = True.
Proof. exact (@lem52707 _5310 (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52709 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) (p2 : _5333) : ((term51 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) = (term52 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)) = True.
Proof. exact (TRANS (@lem52704 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2) (@lem52708 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52710 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) : (term54 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'') = (term173 _5333).
Proof. exact (fun_ext (fun p2 : _5333 => @lem52709 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'' p2)). Qed.
Lemma lem52711 {_5333 : Type'} : (@all _5333) = (@all _5333).
Proof. exact (eq_refl (@all _5333)). Qed.
Lemma lem52712 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) : (term56 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'') = (term174 _5333).
Proof. exact (MK_COMB (@lem52711 _5333) (@lem52710 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'')). Qed.
Lemma lem52714 {A : Type'} (t : Prop) : (term175 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52715 {_5333 : Type'} (t : Prop) : (term175 _5333 t) = t.
Proof. exact (@lem52714 _5333 t). Qed.
Lemma lem52716 {_5333 : Type'} : (term174 _5333) = True.
Proof. exact (@lem52715 _5333 True). Qed.
Lemma lem52717 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) (p1'' : _5334) : (term56 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'') = True.
Proof. exact (TRANS (@lem52712 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'') (@lem52716 _5333)). Qed.
Lemma lem52718 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term58 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term173 _5334).
Proof. exact (fun_ext (fun p1'' : _5334 => @lem52717 _5310 _5326 _5330 _5333 _5334 f p1 p1' p1'')). Qed.
Lemma lem52719 {_5334 : Type'} : (@all _5334) = (@all _5334).
Proof. exact (eq_refl (@all _5334)). Qed.
Lemma lem52720 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term59 _5310 _5326 _5330 _5333 _5334 f p1 p1') = (term174 _5334).
Proof. exact (MK_COMB (@lem52719 _5334) (@lem52718 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52722 {A : Type'} (t : Prop) : (term175 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52723 {_5334 : Type'} (t : Prop) : (term175 _5334 t) = t.
Proof. exact (@lem52722 _5334 t). Qed.
Lemma lem52724 {_5334 : Type'} : (term174 _5334) = True.
Proof. exact (@lem52723 _5334 True). Qed.
Lemma lem52725 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term59 _5310 _5326 _5330 _5333 _5334 f p1 p1') = True.
Proof. exact (TRANS (@lem52720 _5310 _5326 _5330 _5333 _5334 f p1 p1') (@lem52724 _5334)). Qed.
Lemma lem52726 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) (p1' : _5330) : (term40 _5310 _5326 _5330 _5333 _5334 f p1 p1') = True.
Proof. exact (TRANS (@lem52434 _5310 _5326 _5330 _5333 _5334 f p1 p1') (@lem52725 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52727 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term42 _5310 _5326 _5330 _5333 _5334 f p1) = (term173 _5330).
Proof. exact (fun_ext (fun p1' : _5330 => @lem52726 _5310 _5326 _5330 _5333 _5334 f p1 p1')). Qed.
Lemma lem52728 {_5330 : Type'} : (@all _5330) = (@all _5330).
Proof. exact (eq_refl (@all _5330)). Qed.
Lemma lem52729 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term43 _5310 _5326 _5330 _5333 _5334 f p1) = (term174 _5330).
Proof. exact (MK_COMB (@lem52728 _5330) (@lem52727 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52731 {A : Type'} (t : Prop) : (term175 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52732 {_5330 : Type'} (t : Prop) : (term175 _5330 t) = t.
Proof. exact (@lem52731 _5330 t). Qed.
Lemma lem52733 {_5330 : Type'} : (term174 _5330) = True.
Proof. exact (@lem52732 _5330 True). Qed.
Lemma lem52734 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term43 _5310 _5326 _5330 _5333 _5334 f p1) = True.
Proof. exact (TRANS (@lem52729 _5310 _5326 _5330 _5333 _5334 f p1) (@lem52733 _5330)). Qed.
Lemma lem52735 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) (p1 : _5326) : (term22 _5310 _5326 _5330 _5333 _5334 f p1) = True.
Proof. exact (TRANS (@lem52405 _5310 _5326 _5330 _5333 _5334 f p1) (@lem52734 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52736 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term24 _5310 _5326 _5330 _5333 _5334 f) = (term173 _5326).
Proof. exact (fun_ext (fun p1 : _5326 => @lem52735 _5310 _5326 _5330 _5333 _5334 f p1)). Qed.
Lemma lem52737 {_5326 : Type'} : (@all _5326) = (@all _5326).
Proof. exact (eq_refl (@all _5326)). Qed.
Lemma lem52738 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term25 _5310 _5326 _5330 _5333 _5334 f) = (term174 _5326).
Proof. exact (MK_COMB (@lem52737 _5326) (@lem52736 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52740 {A : Type'} (t : Prop) : (term175 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52741 {_5326 : Type'} (t : Prop) : (term175 _5326 t) = t.
Proof. exact (@lem52740 _5326 t). Qed.
Lemma lem52742 {_5326 : Type'} : (term174 _5326) = True.
Proof. exact (@lem52741 _5326 True). Qed.
Lemma lem52743 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term25 _5310 _5326 _5330 _5333 _5334 f) = True.
Proof. exact (TRANS (@lem52738 _5310 _5326 _5330 _5333 _5334 f) (@lem52742 _5326)). Qed.
Lemma lem52744 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : ((term2 _5310 _5326 _5330 _5333 _5334 f) = f) = True.
Proof. exact (TRANS (@lem52382 _5310 _5326 _5330 _5333 _5334 f) (@lem52743 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52745 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : True = ((term2 _5310 _5326 _5330 _5333 _5334 f) = f).
Proof. exact (SYM (@lem52744 _5310 _5326 _5330 _5333 _5334 f)). Qed.
Lemma lem52746 {_5310 _5326 _5330 _5333 _5334 : Type'} (f : type1218 _5310 _5326 _5330 _5333 _5334) : (term2 _5310 _5326 _5330 _5333 _5334 f) = f.
Proof. exact (EQ_MP (@lem52745 _5310 _5326 _5330 _5333 _5334 f) (@lem0)). Qed.
Lemma lem52751 {_5310 _5326 _5330 _5333 _5334 : Type'} : term176 _5310 _5326 _5330 _5333 _5334.
Proof. exact (fun f : type1218 _5310 _5326 _5330 _5333 _5334 => @lem52746 _5310 _5326 _5330 _5333 _5334 f). Qed.
