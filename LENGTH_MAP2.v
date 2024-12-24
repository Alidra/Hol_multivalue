Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_MAP2_term_abbrevs.
Require Import MAP2_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1188383 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1188384 {_27740 : Type'} (P : type1143 _27740) : term0 _27740 P.
Proof. exact (@lem1188383 _27740 P). Qed.
Lemma lem1188385 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term1 _27740 _27742 _27753 f.
Proof. exact (@lem1188384 _27740 (term2 _27740 _27742 _27753 f)). Qed.
Lemma lem1188386 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term3 _27740 _27742 _27753 f) = (term4 _27740 _27742 _27753 f).
Proof. exact (eq_refl (term3 _27740 _27742 _27753 f)). Qed.
Lemma lem1188387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1188388 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term5 _27740 _27742 _27753 f) = (term6 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188387) (@lem1188386 _27740 _27742 _27753 f)). Qed.
Lemma lem1188389 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27740) : (term7 _27740 _27742 _27753 f t) = (term8 _27740 _27742 _27753 f t).
Proof. exact (eq_refl (term7 _27740 _27742 _27753 f t)). Qed.
Lemma lem1188390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188391 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27740) : (term9 _27740 _27742 _27753 f t) = (term10 _27740 _27742 _27753 f t).
Proof. exact (MK_COMB (@lem1188390) (@lem1188389 _27740 _27742 _27753 f t)). Qed.
Lemma lem1188392 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term11 _27740 _27742 _27753 f h t) = (term12 _27740 _27742 _27753 f h t).
Proof. exact (eq_refl (term11 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188393 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term13 _27740 _27742 _27753 f h t) = (term14 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188391 _27740 _27742 _27753 f t) (@lem1188392 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188394 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) : (term15 _27740 _27742 _27753 f h) = (term16 _27740 _27742 _27753 f h).
Proof. exact (fun_ext (fun t : list _27740 => @lem1188393 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188395 {_27740 : Type'} : (@all (list _27740)) = (@all (list _27740)).
Proof. exact (eq_refl (@all (list _27740))). Qed.
Lemma lem1188396 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) : (term17 _27740 _27742 _27753 f h) = (term18 _27740 _27742 _27753 f h).
Proof. exact (MK_COMB (@lem1188395 _27740) (@lem1188394 _27740 _27742 _27753 f h)). Qed.
Lemma lem1188397 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term19 _27740 _27742 _27753 f) = (term20 _27740 _27742 _27753 f).
Proof. exact (fun_ext (fun h : _27740 => @lem1188396 _27740 _27742 _27753 f h)). Qed.
Lemma lem1188398 {_27740 : Type'} : (@all _27740) = (@all _27740).
Proof. exact (eq_refl (@all _27740)). Qed.
Lemma lem1188399 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term21 _27740 _27742 _27753 f) = (term22 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188398 _27740) (@lem1188397 _27740 _27742 _27753 f)). Qed.
Lemma lem1188400 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term23 _27740 _27742 _27753 f) = (term24 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188388 _27740 _27742 _27753 f) (@lem1188399 _27740 _27742 _27753 f)). Qed.
Lemma lem1188401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188402 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term25 _27740 _27742 _27753 f) = (term26 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188401) (@lem1188400 _27740 _27742 _27753 f)). Qed.
Lemma lem1188403 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (l : list _27740) : (term7 _27740 _27742 _27753 f l) = (term8 _27740 _27742 _27753 f l).
Proof. exact (eq_refl (term7 _27740 _27742 _27753 f l)). Qed.
Lemma lem1188404 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term27 _27740 _27742 _27753 f) = (term2 _27740 _27742 _27753 f).
Proof. exact (fun_ext (fun l : list _27740 => @lem1188403 _27740 _27742 _27753 f l)). Qed.
Lemma lem1188405 {_27740 : Type'} : (@all (list _27740)) = (@all (list _27740)).
Proof. exact (eq_refl (@all (list _27740))). Qed.
Lemma lem1188406 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term28 _27740 _27742 _27753 f) = (term29 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188405 _27740) (@lem1188404 _27740 _27742 _27753 f)). Qed.
Lemma lem1188407 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term1 _27740 _27742 _27753 f) = (term30 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188402 _27740 _27742 _27753 f) (@lem1188406 _27740 _27742 _27753 f)). Qed.
Lemma lem1188408 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term30 _27740 _27742 _27753 f.
Proof. exact (EQ_MP (@lem1188407 _27740 _27742 _27753 f) (@lem1188385 _27740 _27742 _27753 f)). Qed.
Lemma lem1188409 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term8 _27740 _27742 _27753 f t.
Proof. exact (h1). Qed.
Lemma lem1188411 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1188412 {_27742 : Type'} (P : type1143 _27742) : term0 _27742 P.
Proof. exact (@lem1188411 _27742 P). Qed.
Lemma lem1188413 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term31 _27740 _27742 _27753 f.
Proof. exact (@lem1188412 _27742 (term32 _27740 _27742 _27753 f)). Qed.
Lemma lem1188414 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term33 _27740 _27742 _27753 f) = (term34 _27740 _27742 _27753 f).
Proof. exact (eq_refl (term33 _27740 _27742 _27753 f)). Qed.
Lemma lem1188415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1188416 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term35 _27740 _27742 _27753 f) = (term36 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188415) (@lem1188414 _27740 _27742 _27753 f)). Qed.
Lemma lem1188417 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27742) : (term37 _27740 _27742 _27753 f t) = (term38 _27740 _27742 _27753 f t).
Proof. exact (eq_refl (term37 _27740 _27742 _27753 f t)). Qed.
Lemma lem1188418 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188419 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27742) : (term39 _27740 _27742 _27753 f t) = (term40 _27740 _27742 _27753 f t).
Proof. exact (MK_COMB (@lem1188418) (@lem1188417 _27740 _27742 _27753 f t)). Qed.
Lemma lem1188420 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : (term41 _27740 _27742 _27753 f h t) = (term42 _27740 _27742 _27753 f h t).
Proof. exact (eq_refl (term41 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188421 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : (term43 _27740 _27742 _27753 f h t) = (term44 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188419 _27740 _27742 _27753 f t) (@lem1188420 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188422 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) : (term45 _27740 _27742 _27753 f h) = (term46 _27740 _27742 _27753 f h).
Proof. exact (fun_ext (fun t : list _27742 => @lem1188421 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188423 {_27742 : Type'} : (@all (list _27742)) = (@all (list _27742)).
Proof. exact (eq_refl (@all (list _27742))). Qed.
Lemma lem1188424 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) : (term47 _27740 _27742 _27753 f h) = (term48 _27740 _27742 _27753 f h).
Proof. exact (MK_COMB (@lem1188423 _27742) (@lem1188422 _27740 _27742 _27753 f h)). Qed.
Lemma lem1188425 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term49 _27740 _27742 _27753 f) = (term50 _27740 _27742 _27753 f).
Proof. exact (fun_ext (fun h : _27742 => @lem1188424 _27740 _27742 _27753 f h)). Qed.
Lemma lem1188426 {_27742 : Type'} : (@all _27742) = (@all _27742).
Proof. exact (eq_refl (@all _27742)). Qed.
Lemma lem1188427 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term51 _27740 _27742 _27753 f) = (term52 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188426 _27742) (@lem1188425 _27740 _27742 _27753 f)). Qed.
Lemma lem1188428 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term53 _27740 _27742 _27753 f) = (term54 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188416 _27740 _27742 _27753 f) (@lem1188427 _27740 _27742 _27753 f)). Qed.
Lemma lem1188429 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188430 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term55 _27740 _27742 _27753 f) = (term56 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188429) (@lem1188428 _27740 _27742 _27753 f)). Qed.
Lemma lem1188431 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (m : list _27742) : (term37 _27740 _27742 _27753 f m) = (term38 _27740 _27742 _27753 f m).
Proof. exact (eq_refl (term37 _27740 _27742 _27753 f m)). Qed.
Lemma lem1188432 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term57 _27740 _27742 _27753 f) = (term32 _27740 _27742 _27753 f).
Proof. exact (fun_ext (fun m : list _27742 => @lem1188431 _27740 _27742 _27753 f m)). Qed.
Lemma lem1188433 {_27742 : Type'} : (@all (list _27742)) = (@all (list _27742)).
Proof. exact (eq_refl (@all (list _27742))). Qed.
Lemma lem1188434 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term58 _27740 _27742 _27753 f) = (term4 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188433 _27742) (@lem1188432 _27740 _27742 _27753 f)). Qed.
Lemma lem1188435 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term31 _27740 _27742 _27753 f) = (term59 _27740 _27742 _27753 f).
Proof. exact (MK_COMB (@lem1188430 _27740 _27742 _27753 f) (@lem1188434 _27740 _27742 _27753 f)). Qed.
Lemma lem1188436 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term59 _27740 _27742 _27753 f.
Proof. exact (EQ_MP (@lem1188435 _27740 _27742 _27753 f) (@lem1188413 _27740 _27742 _27753 f)). Qed.
Lemma lem1188439 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1188440 {_27742 : Type'} (P : type1143 _27742) : term0 _27742 P.
Proof. exact (@lem1188439 _27742 P). Qed.
Lemma lem1188441 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : term60 _27740 _27742 _27753 f h t.
Proof. exact (@lem1188440 _27742 (term61 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188442 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term62 _27740 _27742 _27753 f h t) = (term63 _27740 _27742 _27753 f h t).
Proof. exact (eq_refl (term62 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1188444 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term64 _27740 _27742 _27753 f h t) = (term65 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188443) (@lem1188442 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188445 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (t' : list _27742) : (term66 _27740 _27742 _27753 f h t t') = (term67 _27740 _27742 _27753 f h t t').
Proof. exact (eq_refl (term66 _27740 _27742 _27753 f h t t')). Qed.
Lemma lem1188446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188447 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (t' : list _27742) : (term68 _27740 _27742 _27753 f h t t') = (term69 _27740 _27742 _27753 f h t t').
Proof. exact (MK_COMB (@lem1188446) (@lem1188445 _27740 _27742 _27753 f h t t')). Qed.
Lemma lem1188448 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) : (term70 _27740 _27742 _27753 f h t h' t') = (term71 _27740 _27742 _27753 f h t h' t').
Proof. exact (eq_refl (term70 _27740 _27742 _27753 f h t h' t')). Qed.
Lemma lem1188449 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) : (term72 _27740 _27742 _27753 f h t h' t') = (term73 _27740 _27742 _27753 f h t h' t').
Proof. exact (MK_COMB (@lem1188447 _27740 _27742 _27753 f h t t') (@lem1188448 _27740 _27742 _27753 f h t h' t')). Qed.
Lemma lem1188450 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) : (term74 _27740 _27742 _27753 f h t h') = (term75 _27740 _27742 _27753 f h t h').
Proof. exact (fun_ext (fun t' : list _27742 => @lem1188449 _27740 _27742 _27753 f h t h' t')). Qed.
Lemma lem1188451 {_27742 : Type'} : (@all (list _27742)) = (@all (list _27742)).
Proof. exact (eq_refl (@all (list _27742))). Qed.
Lemma lem1188452 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) : (term76 _27740 _27742 _27753 f h t h') = (term77 _27740 _27742 _27753 f h t h').
Proof. exact (MK_COMB (@lem1188451 _27742) (@lem1188450 _27740 _27742 _27753 f h t h')). Qed.
Lemma lem1188453 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term78 _27740 _27742 _27753 f h t) = (term79 _27740 _27742 _27753 f h t).
Proof. exact (fun_ext (fun h' : _27742 => @lem1188452 _27740 _27742 _27753 f h t h')). Qed.
Lemma lem1188454 {_27742 : Type'} : (@all _27742) = (@all _27742).
Proof. exact (eq_refl (@all _27742)). Qed.
Lemma lem1188455 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term80 _27740 _27742 _27753 f h t) = (term81 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188454 _27742) (@lem1188453 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188456 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term82 _27740 _27742 _27753 f h t) = (term83 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188444 _27740 _27742 _27753 f h t) (@lem1188455 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1188458 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term84 _27740 _27742 _27753 f h t) = (term85 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188457) (@lem1188456 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188459 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (m : list _27742) : (term66 _27740 _27742 _27753 f h t m) = (term67 _27740 _27742 _27753 f h t m).
Proof. exact (eq_refl (term66 _27740 _27742 _27753 f h t m)). Qed.
Lemma lem1188460 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term86 _27740 _27742 _27753 f h t) = (term61 _27740 _27742 _27753 f h t).
Proof. exact (fun_ext (fun m : list _27742 => @lem1188459 _27740 _27742 _27753 f h t m)). Qed.
Lemma lem1188461 {_27742 : Type'} : (@all (list _27742)) = (@all (list _27742)).
Proof. exact (eq_refl (@all (list _27742))). Qed.
Lemma lem1188462 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term87 _27740 _27742 _27753 f h t) = (term12 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188461 _27742) (@lem1188460 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188463 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term60 _27740 _27742 _27753 f h t) = (term88 _27740 _27742 _27753 f h t).
Proof. exact (MK_COMB (@lem1188458 _27740 _27742 _27753 f h t) (@lem1188462 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188464 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : term88 _27740 _27742 _27753 f h t.
Proof. exact (EQ_MP (@lem1188463 _27740 _27742 _27753 f h t) (@lem1188441 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188522 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1188523 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1188522 p q p' q'). Qed.
Lemma lem1188524 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1188523 p q p'). Qed.
Lemma lem1188525 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term92 _27740 _27742 _27753 f.
Proof. exact (@lem1188524 ((@List.length _27740 (@nil _27740)) = (@List.length _27742 (@nil _27742))) ((term93 _27740 _27742 _27753 f) = (@List.length _27742 (@nil _27742)))). Qed.
Lemma lem1188526 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (p' : Prop) : term94 _27740 _27742 _27753 f p'.
Proof. exact (@lem1188525 _27740 _27742 _27753 f p'). Qed.
Lemma lem1188527 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (p' : Prop) : (term94 _27740 _27742 _27753 f p') = (term95 _27740 _27742 _27753 f p').
Proof. exact (eq_refl (term94 _27740 _27742 _27753 f p')). Qed.
Lemma lem1188528 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (p' : Prop) : term95 _27740 _27742 _27753 f p'.
Proof. exact (EQ_MP (@lem1188527 _27740 _27742 _27753 f p') (@lem1188526 _27740 _27742 _27753 f p')). Qed.
Lemma lem1188529 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (p' : Prop) (q' : Prop) : term96 _27740 _27742 _27753 f p' q'.
Proof. exact (@lem1188528 _27740 _27742 _27753 f p' q'). Qed.
Lemma lem1188530 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (p' : Prop) (q' : Prop) : (term96 _27740 _27742 _27753 f p' q') = (term97 _27740 _27742 _27753 f p' q').
Proof. exact (eq_refl (term96 _27740 _27742 _27753 f p' q')). Qed.
Lemma lem1188531 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (p' : Prop) (q' : Prop) : term97 _27740 _27742 _27753 f p' q'.
Proof. exact (EQ_MP (@lem1188530 _27740 _27742 _27753 f p' q') (@lem1188529 _27740 _27742 _27753 f p' q')). Qed.
Lemma lem1188535 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1188536 {_27740 : Type'} : (@List.length _27740 (@nil _27740)) = (NUMERAL 0).
Proof. exact (@lem1188535 _27740). Qed.
Lemma lem1188537 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1188538 {_27740 : Type'} : (term98 _27740) = term99.
Proof. exact (MK_COMB (@lem1188537) (@lem1188536 _27740)). Qed.
Lemma lem1188540 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1188541 {_27742 : Type'} : (@List.length _27742 (@nil _27742)) = (NUMERAL 0).
Proof. exact (@lem1188540 _27742). Qed.
Lemma lem1188542 {_27740 _27742 : Type'} : ((@List.length _27740 (@nil _27740)) = (@List.length _27742 (@nil _27742))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1188538 _27740) (@lem1188541 _27742)). Qed.
Lemma lem1188544 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1188545 (x : nat) : (x = x) = True.
Proof. exact (@lem1188544 nat x). Qed.
Lemma lem1188546 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1188545 (NUMERAL 0)). Qed.
Lemma lem1188547 {_27740 _27742 : Type'} : ((@List.length _27740 (@nil _27740)) = (@List.length _27742 (@nil _27742))) = True.
Proof. exact (TRANS (@lem1188542 _27740 _27742) (@lem1188546)). Qed.
Lemma lem1188548 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (q' : Prop) : term100 _27740 _27742 _27753 f q'.
Proof. exact (@lem1188531 _27740 _27742 _27753 f True q'). Qed.
Lemma lem1188549 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (q' : Prop) : term101 _27740 _27742 _27753 f q'.
Proof. exact (@lem1188548 _27740 _27742 _27753 f q' (@lem1188547 _27740 _27742)). Qed.
Lemma lem1188558 {_25542 _25543 _25549 : Type'} (f : type1469 _25542 _25543 _25549) : (@MAP2 _25549 _25543 _25542 f (@nil _25543) (@nil _25542)) = (@nil _25549).
Proof. exact (proj1 (@lem1105126 _25542 _25543 _25549 (@el _25543) (@el _25542) f (@el (list _25543)) (@el (list _25542)))). Qed.
Lemma lem1188559 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (@MAP2 _27753 _27740 _27742 f (@nil _27740) (@nil _27742)) = (@nil _27753).
Proof. exact (@lem1188558 _27742 _27740 _27753 f). Qed.
Lemma lem1188560 {_27753 : Type'} : (@List.length _27753) = (@List.length _27753).
Proof. exact (eq_refl (@List.length _27753)). Qed.
Lemma lem1188561 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term93 _27740 _27742 _27753 f) = (@List.length _27753 (@nil _27753)).
Proof. exact (MK_COMB (@lem1188560 _27753) (@lem1188559 _27740 _27742 _27753 f)). Qed.
Lemma lem1188563 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1188564 {_27753 : Type'} : (@List.length _27753 (@nil _27753)) = (NUMERAL 0).
Proof. exact (@lem1188563 _27753). Qed.
Lemma lem1188565 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term93 _27740 _27742 _27753 f) = (NUMERAL 0).
Proof. exact (TRANS (@lem1188561 _27740 _27742 _27753 f) (@lem1188564 _27753)). Qed.
Lemma lem1188566 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1188567 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term102 _27740 _27742 _27753 f) = term99.
Proof. exact (MK_COMB (@lem1188566) (@lem1188565 _27740 _27742 _27753 f)). Qed.
Lemma lem1188569 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1188570 {_27742 : Type'} : (@List.length _27742 (@nil _27742)) = (NUMERAL 0).
Proof. exact (@lem1188569 _27742). Qed.
Lemma lem1188571 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : ((term93 _27740 _27742 _27753 f) = (@List.length _27742 (@nil _27742))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1188567 _27740 _27742 _27753 f) (@lem1188570 _27742)). Qed.
Lemma lem1188573 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1188574 (x : nat) : (x = x) = True.
Proof. exact (@lem1188573 nat x). Qed.
Lemma lem1188575 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1188574 (NUMERAL 0)). Qed.
Lemma lem1188578 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : ((term93 _27740 _27742 _27753 f) = (@List.length _27742 (@nil _27742))) = True.
Proof. exact (TRANS (@lem1188571 _27740 _27742 _27753 f) (@lem1188575)). Qed.
Lemma lem1188579 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term103 _27740 _27742 _27753 f.
Proof. exact (fun h0 : True => @lem1188578 _27740 _27742 _27753 f). Qed.
Lemma lem1188580 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term104 _27740 _27742 _27753 f.
Proof. exact (@lem1188549 _27740 _27742 _27753 f True). Qed.
Lemma lem1188581 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term34 _27740 _27742 _27753 f) = (True -> True).
Proof. exact (@lem1188580 _27740 _27742 _27753 f (@lem1188579 _27740 _27742 _27753 f)). Qed.
Lemma lem1188583 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1188584 : (True -> True) = True.
Proof. exact (@lem1188583 True). Qed.
Lemma lem1188585 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : (term34 _27740 _27742 _27753 f) = True.
Proof. exact (TRANS (@lem1188581 _27740 _27742 _27753 f) (@lem1188584)). Qed.
Lemma lem1188586 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : True = (term34 _27740 _27742 _27753 f).
Proof. exact (SYM (@lem1188585 _27740 _27742 _27753 f)). Qed.
Lemma lem1188587 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term34 _27740 _27742 _27753 f.
Proof. exact (EQ_MP (@lem1188586 _27740 _27742 _27753 f) (@lem0)). Qed.
Lemma lem1188596 (n : nat) : term105 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1188597 (n : nat) : (term105 n) = (term106 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem1188598 (n : nat) : term106 n.
Proof. exact (EQ_MP (@lem1188597 n) (@lem1188596 n)). Qed.
Lemma lem1188602 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1188603 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1188602 n h1)). Qed.
Lemma lem1188604 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1188605 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1188604 n h1)). Qed.
Lemma lem1188606 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem1188603 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem1188605 n h1)). Qed.
Lemma lem1188607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1188608 (n : nat) : (term106 n) = (term107 n).
Proof. exact (MK_COMB (@lem1188607) (@lem1188606 n)). Qed.
Lemma lem1188609 (n : nat) : term107 n.
Proof. exact (EQ_MP (@lem1188608 n) (@lem1188598 n)). Qed.
Lemma lem1188610 (n : nat) : term108 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem1188631 {A : Type'} : term109 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1188632 {A : Type'} (h : A) : term110 A h.
Proof. exact (@lem1188631 A h). Qed.
Lemma lem1188633 {A : Type'} (h : A) : (term110 A h) = (term111 A h).
Proof. exact (eq_refl (term110 A h)). Qed.
Lemma lem1188634 {A : Type'} (h : A) : term111 A h.
Proof. exact (EQ_MP (@lem1188633 A h) (@lem1188632 A h)). Qed.
Lemma lem1188635 {A : Type'} (h : A) (t : list A) : term112 A h t.
Proof. exact (@lem1188634 A h t). Qed.
Lemma lem1188636 {A : Type'} (h : A) (t : list A) : (term112 A h t) = ((term113 A h t) = (term114 A t)).
Proof. exact (eq_refl (term112 A h t)). Qed.
Lemma lem1188651 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1188652 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1188651 p q p' q'). Qed.
Lemma lem1188653 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1188652 p q p'). Qed.
Lemma lem1188654 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : term115 _27740 _27742 _27753 f h t.
Proof. exact (@lem1188653 ((@List.length _27740 (@nil _27740)) = (term113 _27742 h t)) ((term116 _27740 _27742 _27753 f h t) = (term113 _27742 h t))). Qed.
Lemma lem1188655 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (p' : Prop) : term117 _27740 _27742 _27753 f h t p'.
Proof. exact (@lem1188654 _27740 _27742 _27753 f h t p'). Qed.
Lemma lem1188656 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (p' : Prop) : (term117 _27740 _27742 _27753 f h t p') = (term118 _27740 _27742 _27753 f h t p').
Proof. exact (eq_refl (term117 _27740 _27742 _27753 f h t p')). Qed.
Lemma lem1188657 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (p' : Prop) : term118 _27740 _27742 _27753 f h t p'.
Proof. exact (EQ_MP (@lem1188656 _27740 _27742 _27753 f h t p') (@lem1188655 _27740 _27742 _27753 f h t p')). Qed.
Lemma lem1188658 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (p' : Prop) (q' : Prop) : term119 _27740 _27742 _27753 f h t p' q'.
Proof. exact (@lem1188657 _27740 _27742 _27753 f h t p' q'). Qed.
Lemma lem1188659 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (p' : Prop) (q' : Prop) : (term119 _27740 _27742 _27753 f h t p' q') = (term120 _27740 _27742 _27753 f h t p' q').
Proof. exact (eq_refl (term119 _27740 _27742 _27753 f h t p' q')). Qed.
Lemma lem1188660 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (p' : Prop) (q' : Prop) : term120 _27740 _27742 _27753 f h t p' q'.
Proof. exact (EQ_MP (@lem1188659 _27740 _27742 _27753 f h t p' q') (@lem1188658 _27740 _27742 _27753 f h t p' q')). Qed.
Lemma lem1188664 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1188665 {_27740 : Type'} : (@List.length _27740 (@nil _27740)) = (NUMERAL 0).
Proof. exact (@lem1188664 _27740). Qed.
Lemma lem1188666 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1188667 {_27740 : Type'} : (term98 _27740) = term99.
Proof. exact (MK_COMB (@lem1188666) (@lem1188665 _27740)). Qed.
Lemma lem1188669 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1188636 A h t) (@lem1188635 A h t)). Qed.
Lemma lem1188670 {_27742 : Type'} (h : _27742) (t : list _27742) : (term113 _27742 h t) = (term114 _27742 t).
Proof. exact (@lem1188669 _27742 h t). Qed.
Lemma lem1188671 {_27740 _27742 : Type'} (h : _27742) (t : list _27742) : ((@List.length _27740 (@nil _27740)) = (term113 _27742 h t)) = ((NUMERAL 0) = (term114 _27742 t)).
Proof. exact (MK_COMB (@lem1188667 _27740) (@lem1188670 _27742 h t)). Qed.
Lemma lem1188673 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem1188610 n (@lem1188609 n)). Qed.
Lemma lem1188674 {_27742 : Type'} (t : list _27742) : ((NUMERAL 0) = (term114 _27742 t)) = False.
Proof. exact (@lem1188673 (@List.length _27742 t)). Qed.
Lemma lem1188675 {_27740 _27742 : Type'} (h : _27742) (t : list _27742) : ((@List.length _27740 (@nil _27740)) = (term113 _27742 h t)) = False.
Proof. exact (TRANS (@lem1188671 _27740 _27742 h t) (@lem1188674 _27742 t)). Qed.
Lemma lem1188676 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (q' : Prop) : term121 _27740 _27742 _27753 f h t q'.
Proof. exact (@lem1188660 _27740 _27742 _27753 f h t False q'). Qed.
Lemma lem1188677 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) (q' : Prop) : term122 _27740 _27742 _27753 f h t q'.
Proof. exact (@lem1188676 _27740 _27742 _27753 f h t q' (@lem1188675 _27740 _27742 h t)). Qed.
Lemma lem1188684 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1188636 A h t) (@lem1188635 A h t)). Qed.
Lemma lem1188685 {_27742 : Type'} (h : _27742) (t : list _27742) : (term113 _27742 h t) = (term114 _27742 t).
Proof. exact (@lem1188684 _27742 h t). Qed.
Lemma lem1188686 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : (term123 _27740 _27742 _27753 f h t) = (term123 _27740 _27742 _27753 f h t).
Proof. exact (eq_refl (term123 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188687 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : ((term116 _27740 _27742 _27753 f h t) = (term113 _27742 h t)) = ((term116 _27740 _27742 _27753 f h t) = (term114 _27742 t)).
Proof. exact (MK_COMB (@lem1188686 _27740 _27742 _27753 f h t) (@lem1188685 _27742 h t)). Qed.
Lemma lem1188690 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : term124 _27740 _27742 _27753 f h t.
Proof. exact (fun h0 : False => @lem1188687 _27740 _27742 _27753 f h t). Qed.
Lemma lem1188691 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : term125 _27740 _27742 _27753 f h t.
Proof. exact (@lem1188677 _27740 _27742 _27753 f h t ((term116 _27740 _27742 _27753 f h t) = (term114 _27742 t))). Qed.
Lemma lem1188692 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : (term42 _27740 _27742 _27753 f h t) = (term126 _27740 _27742 _27753 f h t).
Proof. exact (@lem1188691 _27740 _27742 _27753 f h t (@lem1188690 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188694 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1188695 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : (term126 _27740 _27742 _27753 f h t) = True.
Proof. exact (@lem1188694 ((term116 _27740 _27742 _27753 f h t) = (term114 _27742 t))). Qed.
Lemma lem1188696 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : (term42 _27740 _27742 _27753 f h t) = True.
Proof. exact (TRANS (@lem1188692 _27740 _27742 _27753 f h t) (@lem1188695 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188697 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : True = (term42 _27740 _27742 _27753 f h t).
Proof. exact (SYM (@lem1188696 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188698 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : term42 _27740 _27742 _27753 f h t.
Proof. exact (EQ_MP (@lem1188697 _27740 _27742 _27753 f h t) (@lem0)). Qed.
Lemma lem1188707 (n : nat) : term105 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1188708 (n : nat) : (term105 n) = (term106 n).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem1188709 (n : nat) : term106 n.
Proof. exact (EQ_MP (@lem1188708 n) (@lem1188707 n)). Qed.
Lemma lem1188710 (n : nat) : term127 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1188742 {A : Type'} : term109 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1188743 {A : Type'} (h : A) : term110 A h.
Proof. exact (@lem1188742 A h). Qed.
Lemma lem1188744 {A : Type'} (h : A) : (term110 A h) = (term111 A h).
Proof. exact (eq_refl (term110 A h)). Qed.
Lemma lem1188745 {A : Type'} (h : A) : term111 A h.
Proof. exact (EQ_MP (@lem1188744 A h) (@lem1188743 A h)). Qed.
Lemma lem1188746 {A : Type'} (h : A) (t : list A) : term112 A h t.
Proof. exact (@lem1188745 A h t). Qed.
Lemma lem1188747 {A : Type'} (h : A) (t : list A) : (term112 A h t) = ((term113 A h t) = (term114 A t)).
Proof. exact (eq_refl (term112 A h t)). Qed.
Lemma lem1188765 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1188766 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1188765 p q p' q'). Qed.
Lemma lem1188767 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1188766 p q p'). Qed.
Lemma lem1188768 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : term128 _27740 _27742 _27753 f h t.
Proof. exact (@lem1188767 ((term113 _27740 h t) = (@List.length _27742 (@nil _27742))) ((term129 _27740 _27742 _27753 f h t) = (@List.length _27742 (@nil _27742)))). Qed.
Lemma lem1188769 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (p' : Prop) : term130 _27740 _27742 _27753 f h t p'.
Proof. exact (@lem1188768 _27740 _27742 _27753 f h t p'). Qed.
Lemma lem1188770 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (p' : Prop) : (term130 _27740 _27742 _27753 f h t p') = (term131 _27740 _27742 _27753 f h t p').
Proof. exact (eq_refl (term130 _27740 _27742 _27753 f h t p')). Qed.
Lemma lem1188771 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (p' : Prop) : term131 _27740 _27742 _27753 f h t p'.
Proof. exact (EQ_MP (@lem1188770 _27740 _27742 _27753 f h t p') (@lem1188769 _27740 _27742 _27753 f h t p')). Qed.
Lemma lem1188772 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (p' : Prop) (q' : Prop) : term132 _27740 _27742 _27753 f h t p' q'.
Proof. exact (@lem1188771 _27740 _27742 _27753 f h t p' q'). Qed.
Lemma lem1188773 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (p' : Prop) (q' : Prop) : (term132 _27740 _27742 _27753 f h t p' q') = (term133 _27740 _27742 _27753 f h t p' q').
Proof. exact (eq_refl (term132 _27740 _27742 _27753 f h t p' q')). Qed.
Lemma lem1188774 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (p' : Prop) (q' : Prop) : term133 _27740 _27742 _27753 f h t p' q'.
Proof. exact (EQ_MP (@lem1188773 _27740 _27742 _27753 f h t p' q') (@lem1188772 _27740 _27742 _27753 f h t p' q')). Qed.
Lemma lem1188778 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1188747 A h t) (@lem1188746 A h t)). Qed.
Lemma lem1188779 {_27740 : Type'} (h : _27740) (t : list _27740) : (term113 _27740 h t) = (term114 _27740 t).
Proof. exact (@lem1188778 _27740 h t). Qed.
Lemma lem1188780 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1188781 {_27740 : Type'} (h : _27740) (t : list _27740) : (term134 _27740 h t) = (term135 _27740 t).
Proof. exact (MK_COMB (@lem1188780) (@lem1188779 _27740 h t)). Qed.
Lemma lem1188783 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1188784 {_27742 : Type'} : (@List.length _27742 (@nil _27742)) = (NUMERAL 0).
Proof. exact (@lem1188783 _27742). Qed.
Lemma lem1188785 {_27740 _27742 : Type'} (h : _27740) (t : list _27740) : ((term113 _27740 h t) = (@List.length _27742 (@nil _27742))) = ((term114 _27740 t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1188781 _27740 h t) (@lem1188784 _27742)). Qed.
Lemma lem1188787 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1188710 n (@lem1188709 n)). Qed.
Lemma lem1188788 {_27740 : Type'} (t : list _27740) : ((term114 _27740 t) = (NUMERAL 0)) = False.
Proof. exact (@lem1188787 (@List.length _27740 t)). Qed.
Lemma lem1188789 {_27740 _27742 : Type'} (h : _27740) (t : list _27740) : ((term113 _27740 h t) = (@List.length _27742 (@nil _27742))) = False.
Proof. exact (TRANS (@lem1188785 _27740 _27742 h t) (@lem1188788 _27740 t)). Qed.
Lemma lem1188790 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (q' : Prop) : term136 _27740 _27742 _27753 f h t q'.
Proof. exact (@lem1188774 _27740 _27742 _27753 f h t False q'). Qed.
Lemma lem1188791 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (q' : Prop) : term137 _27740 _27742 _27753 f h t q'.
Proof. exact (@lem1188790 _27740 _27742 _27753 f h t q' (@lem1188789 _27740 _27742 h t)). Qed.
Lemma lem1188798 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1188799 {_27742 : Type'} : (@List.length _27742 (@nil _27742)) = (NUMERAL 0).
Proof. exact (@lem1188798 _27742). Qed.
Lemma lem1188800 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term138 _27740 _27742 _27753 f h t) = (term138 _27740 _27742 _27753 f h t).
Proof. exact (eq_refl (term138 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188801 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : ((term129 _27740 _27742 _27753 f h t) = (@List.length _27742 (@nil _27742))) = ((term129 _27740 _27742 _27753 f h t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1188800 _27740 _27742 _27753 f h t) (@lem1188799 _27742)). Qed.
Lemma lem1188804 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : term139 _27740 _27742 _27753 f h t.
Proof. exact (fun h0 : False => @lem1188801 _27740 _27742 _27753 f h t). Qed.
Lemma lem1188805 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : term140 _27740 _27742 _27753 f h t.
Proof. exact (@lem1188791 _27740 _27742 _27753 f h t ((term129 _27740 _27742 _27753 f h t) = (NUMERAL 0))). Qed.
Lemma lem1188806 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term63 _27740 _27742 _27753 f h t) = (term141 _27740 _27742 _27753 f h t).
Proof. exact (@lem1188805 _27740 _27742 _27753 f h t (@lem1188804 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188808 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1188809 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term141 _27740 _27742 _27753 f h t) = True.
Proof. exact (@lem1188808 ((term129 _27740 _27742 _27753 f h t) = (NUMERAL 0))). Qed.
Lemma lem1188810 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : (term63 _27740 _27742 _27753 f h t) = True.
Proof. exact (TRANS (@lem1188806 _27740 _27742 _27753 f h t) (@lem1188809 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188811 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : True = (term63 _27740 _27742 _27753 f h t).
Proof. exact (SYM (@lem1188810 _27740 _27742 _27753 f h t)). Qed.
Lemma lem1188812 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : term63 _27740 _27742 _27753 f h t.
Proof. exact (EQ_MP (@lem1188811 _27740 _27742 _27753 f h t) (@lem0)). Qed.
Lemma lem1188813 (m : nat) : term142 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1188814 (m : nat) : (term142 m) = (term143 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem1188815 (m : nat) : term143 m.
Proof. exact (EQ_MP (@lem1188814 m) (@lem1188813 m)). Qed.
Lemma lem1188816 (m : nat) (n : nat) : term144 m n.
Proof. exact (@lem1188815 m n). Qed.
Lemma lem1188817 (m : nat) (n : nat) : (term144 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term144 m n)). Qed.
Lemma lem1188856 {A : Type'} : term109 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1188857 {A : Type'} (h : A) : term110 A h.
Proof. exact (@lem1188856 A h). Qed.
Lemma lem1188858 {A : Type'} (h : A) : (term110 A h) = (term111 A h).
Proof. exact (eq_refl (term110 A h)). Qed.
Lemma lem1188859 {A : Type'} (h : A) : term111 A h.
Proof. exact (EQ_MP (@lem1188858 A h) (@lem1188857 A h)). Qed.
Lemma lem1188860 {A : Type'} (h : A) (t : list A) : term112 A h t.
Proof. exact (@lem1188859 A h t). Qed.
Lemma lem1188861 {A : Type'} (h : A) (t : list A) : (term112 A h t) = ((term113 A h t) = (term114 A t)).
Proof. exact (eq_refl (term112 A h t)). Qed.
Lemma lem1188864 {_27740 _27742 _27753 : Type'} (m : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term145 _27740 _27742 _27753 f t m.
Proof. exact (@lem1188409 _27740 _27742 _27753 f t h1 m). Qed.
Lemma lem1188865 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27740) (m : list _27742) : (term145 _27740 _27742 _27753 f t m) = (term146 _27740 _27742 _27753 f t m).
Proof. exact (eq_refl (term145 _27740 _27742 _27753 f t m)). Qed.
Lemma lem1188866 {_27740 _27742 _27753 : Type'} (m : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term146 _27740 _27742 _27753 f t m.
Proof. exact (EQ_MP (@lem1188865 _27740 _27742 _27753 f t m) (@lem1188864 _27740 _27742 _27753 m f t h1)). Qed.
Lemma lem1188867 {_27740 _27742 : Type'} (t : list _27740) (m : list _27742) (h1 : (@List.length _27740 t) = (@List.length _27742 m)) : (@List.length _27740 t) = (@List.length _27742 m).
Proof. exact (h1). Qed.
Lemma lem1188868 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27740) (m : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 m)) : (term147 _27740 _27742 _27753 f t m) = (@List.length _27742 m).
Proof. exact (@lem1188866 _27740 _27742 _27753 m f t h1 (@lem1188867 _27740 _27742 t m h2)). Qed.
Lemma lem1188886 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1188887 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem1188886 p q p' q'). Qed.
Lemma lem1188888 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem1188887 p q p'). Qed.
Lemma lem1188889 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) : term148 _27740 _27742 _27753 f h t h' t'.
Proof. exact (@lem1188888 ((term113 _27740 h t) = (term113 _27742 h' t')) ((term149 _27740 _27742 _27753 f h t h' t') = (term113 _27742 h' t'))). Qed.
Lemma lem1188890 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) (p' : Prop) : term150 _27740 _27742 _27753 f h t h' t' p'.
Proof. exact (@lem1188889 _27740 _27742 _27753 f h t h' t' p'). Qed.
Lemma lem1188891 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) (p' : Prop) : (term150 _27740 _27742 _27753 f h t h' t' p') = (term151 _27740 _27742 _27753 f h t h' t' p').
Proof. exact (eq_refl (term150 _27740 _27742 _27753 f h t h' t' p')). Qed.
Lemma lem1188892 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) (p' : Prop) : term151 _27740 _27742 _27753 f h t h' t' p'.
Proof. exact (EQ_MP (@lem1188891 _27740 _27742 _27753 f h t h' t' p') (@lem1188890 _27740 _27742 _27753 f h t h' t' p')). Qed.
Lemma lem1188893 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) (p' : Prop) (q' : Prop) : term152 _27740 _27742 _27753 f h t h' t' p' q'.
Proof. exact (@lem1188892 _27740 _27742 _27753 f h t h' t' p' q'). Qed.
Lemma lem1188894 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) (p' : Prop) (q' : Prop) : (term152 _27740 _27742 _27753 f h t h' t' p' q') = (term153 _27740 _27742 _27753 f h t h' t' p' q').
Proof. exact (eq_refl (term152 _27740 _27742 _27753 f h t h' t' p' q')). Qed.
Lemma lem1188895 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) (h' : _27742) (t' : list _27742) (p' : Prop) (q' : Prop) : term153 _27740 _27742 _27753 f h t h' t' p' q'.
Proof. exact (EQ_MP (@lem1188894 _27740 _27742 _27753 f h t h' t' p' q') (@lem1188893 _27740 _27742 _27753 f h t h' t' p' q')). Qed.
Lemma lem1188899 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1188861 A h t) (@lem1188860 A h t)). Qed.
Lemma lem1188900 {_27740 : Type'} (h : _27740) (t : list _27740) : (term113 _27740 h t) = (term114 _27740 t).
Proof. exact (@lem1188899 _27740 h t). Qed.
Lemma lem1188901 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1188902 {_27740 : Type'} (h : _27740) (t : list _27740) : (term134 _27740 h t) = (term135 _27740 t).
Proof. exact (MK_COMB (@lem1188901) (@lem1188900 _27740 h t)). Qed.
Lemma lem1188904 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1188861 A h t) (@lem1188860 A h t)). Qed.
Lemma lem1188905 {_27742 : Type'} (h : _27742) (t : list _27742) : (term113 _27742 h t) = (term114 _27742 t).
Proof. exact (@lem1188904 _27742 h t). Qed.
Lemma lem1188906 {_27742 : Type'} (h' : _27742) (t' : list _27742) : (term113 _27742 h' t') = (term114 _27742 t').
Proof. exact (@lem1188905 _27742 h' t'). Qed.
Lemma lem1188907 {_27740 _27742 : Type'} (h : _27740) (h' : _27742) (t : list _27740) (t' : list _27742) : ((term113 _27740 h t) = (term113 _27742 h' t')) = ((term114 _27740 t) = (term114 _27742 t')).
Proof. exact (MK_COMB (@lem1188902 _27740 h t) (@lem1188906 _27742 h' t')). Qed.
Lemma lem1188909 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1188817 m n) (@lem1188816 m n)). Qed.
Lemma lem1188910 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) : ((term114 _27740 t) = (term114 _27742 t')) = ((@List.length _27740 t) = (@List.length _27742 t')).
Proof. exact (@lem1188909 (@List.length _27740 t) (@List.length _27742 t')). Qed.
Lemma lem1188913 {_27740 _27742 : Type'} (h : _27740) (h' : _27742) (t : list _27740) (t' : list _27742) : ((term113 _27740 h t) = (term113 _27742 h' t')) = ((@List.length _27740 t) = (@List.length _27742 t')).
Proof. exact (TRANS (@lem1188907 _27740 _27742 h h' t t') (@lem1188910 _27740 _27742 t t')). Qed.
Lemma lem1188914 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (h' : _27742) (t : list _27740) (t' : list _27742) (q' : Prop) : term154 _27740 _27742 _27753 f h h' t t' q'.
Proof. exact (@lem1188895 _27740 _27742 _27753 f h t h' t' ((@List.length _27740 t) = (@List.length _27742 t')) q'). Qed.
Lemma lem1188915 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (h' : _27742) (t : list _27740) (t' : list _27742) (q' : Prop) : term155 _27740 _27742 _27753 f h h' t t' q'.
Proof. exact (@lem1188914 _27740 _27742 _27753 f h h' t t' q' (@lem1188913 _27740 _27742 h h' t t')). Qed.
Lemma lem1188920 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term156 _25542 _25543 _25549 f h1' t1 h2' t2) = (term157 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (proj2 (@lem1105126 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1188921 {_27740 _27742 _27753 : Type'} (h1' : _27740) (h2' : _27742) (f : type1412 _27740 _27742 _27753) (t1 : list _27740) (t2 : list _27742) : (term158 _27740 _27742 _27753 f h1' t1 h2' t2) = (term159 _27740 _27742 _27753 h1' h2' f t1 t2).
Proof. exact (@lem1188920 _27742 _27740 _27753 h1' h2' f t1 t2). Qed.
Lemma lem1188922 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) : (term158 _27740 _27742 _27753 f h t h' t') = (term159 _27740 _27742 _27753 h h' f t t').
Proof. exact (@lem1188921 _27740 _27742 _27753 h h' f t t'). Qed.
Lemma lem1188923 {_27753 : Type'} : (@List.length _27753) = (@List.length _27753).
Proof. exact (eq_refl (@List.length _27753)). Qed.
Lemma lem1188924 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) : (term149 _27740 _27742 _27753 f h t h' t') = (term160 _27740 _27742 _27753 h h' f t t').
Proof. exact (MK_COMB (@lem1188923 _27753) (@lem1188922 _27740 _27742 _27753 h h' f t t')). Qed.
Lemma lem1188926 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1188861 A h t) (@lem1188860 A h t)). Qed.
Lemma lem1188927 {_27753 : Type'} (h : _27753) (t : list _27753) : (term113 _27753 h t) = (term114 _27753 t).
Proof. exact (@lem1188926 _27753 h t). Qed.
Lemma lem1188928 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) : (term160 _27740 _27742 _27753 h h' f t t') = (term161 _27740 _27742 _27753 f t t').
Proof. exact (@lem1188927 _27753 (f h h') (@MAP2 _27753 _27740 _27742 f t t')). Qed.
Lemma lem1188930 {_27740 _27742 _27753 : Type'} (m : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term146 _27740 _27742 _27753 f t m.
Proof. exact (fun h0 : (@List.length _27740 t) = (@List.length _27742 m) => @lem1188868 _27740 _27742 _27753 f t m h1 h0). Qed.
Lemma lem1188931 {_27740 _27742 _27753 : Type'} (m : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term146 _27740 _27742 _27753 f t m.
Proof. exact (@lem1188930 _27740 _27742 _27753 m f t h1). Qed.
Lemma lem1188932 {_27740 _27742 _27753 : Type'} (t' : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term146 _27740 _27742 _27753 f t t'.
Proof. exact (@lem1188931 _27740 _27742 _27753 t' f t h1). Qed.
Lemma lem1188936 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) (h1 : (@List.length _27740 t) = (@List.length _27742 t')) : (@List.length _27740 t) = (@List.length _27742 t').
Proof. exact (h1). Qed.
Lemma lem1188937 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1188938 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) (h1 : (@List.length _27740 t) = (@List.length _27742 t')) : (term162 _27740 t) = (term162 _27742 t').
Proof. exact (MK_COMB (@lem1188937) (@lem1188936 _27740 _27742 t t' h1)). Qed.
Lemma lem1188939 {_27742 : Type'} (t' : list _27742) : (@List.length _27742 t') = (@List.length _27742 t').
Proof. exact (eq_refl (@List.length _27742 t')). Qed.
Lemma lem1188940 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) (h1 : (@List.length _27740 t) = (@List.length _27742 t')) : ((@List.length _27740 t) = (@List.length _27742 t')) = ((@List.length _27742 t') = (@List.length _27742 t')).
Proof. exact (MK_COMB (@lem1188938 _27740 _27742 t t' h1) (@lem1188939 _27742 t')). Qed.
Lemma lem1188942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1188943 (x : nat) : (x = x) = True.
Proof. exact (@lem1188942 nat x). Qed.
Lemma lem1188944 {_27742 : Type'} (t' : list _27742) : ((@List.length _27742 t') = (@List.length _27742 t')) = True.
Proof. exact (@lem1188943 (@List.length _27742 t')). Qed.
Lemma lem1188945 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) (h1 : (@List.length _27740 t) = (@List.length _27742 t')) : ((@List.length _27740 t) = (@List.length _27742 t')) = True.
Proof. exact (TRANS (@lem1188940 _27740 _27742 t t' h1) (@lem1188944 _27742 t')). Qed.
Lemma lem1188946 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) (h1 : (@List.length _27740 t) = (@List.length _27742 t')) : True = ((@List.length _27740 t) = (@List.length _27742 t')).
Proof. exact (SYM (@lem1188945 _27740 _27742 t t' h1)). Qed.
Lemma lem1188947 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) (h1 : (@List.length _27740 t) = (@List.length _27742 t')) : (@List.length _27740 t) = (@List.length _27742 t').
Proof. exact (EQ_MP (@lem1188946 _27740 _27742 t t' h1) (@lem0)). Qed.
Lemma lem1188948 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 t')) : (term147 _27740 _27742 _27753 f t t') = (@List.length _27742 t').
Proof. exact (@lem1188932 _27740 _27742 _27753 t' f t h1 (@lem1188947 _27740 _27742 t t' h2)). Qed.
Lemma lem1188949 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1188950 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 t')) : (term161 _27740 _27742 _27753 f t t') = (term114 _27742 t').
Proof. exact (MK_COMB (@lem1188949) (@lem1188948 _27740 _27742 _27753 f t t' h1 h2)). Qed.
Lemma lem1188951 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 t')) : (term160 _27740 _27742 _27753 h h' f t t') = (term114 _27742 t').
Proof. exact (TRANS (@lem1188928 _27740 _27742 _27753 h h' f t t') (@lem1188950 _27740 _27742 _27753 f t t' h1 h2)). Qed.
Lemma lem1188952 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 t')) : (term149 _27740 _27742 _27753 f h t h' t') = (term114 _27742 t').
Proof. exact (TRANS (@lem1188924 _27740 _27742 _27753 h h' f t t') (@lem1188951 _27740 _27742 _27753 h h' f t t' h1 h2)). Qed.
Lemma lem1188953 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1188954 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 t')) : (term163 _27740 _27742 _27753 f h t h' t') = (term135 _27742 t').
Proof. exact (MK_COMB (@lem1188953) (@lem1188952 _27740 _27742 _27753 h h' f t t' h1 h2)). Qed.
Lemma lem1188956 {A : Type'} (h : A) (t : list A) : (term113 A h t) = (term114 A t).
Proof. exact (EQ_MP (@lem1188861 A h t) (@lem1188860 A h t)). Qed.
Lemma lem1188957 {_27742 : Type'} (h : _27742) (t : list _27742) : (term113 _27742 h t) = (term114 _27742 t).
Proof. exact (@lem1188956 _27742 h t). Qed.
Lemma lem1188958 {_27742 : Type'} (h' : _27742) (t' : list _27742) : (term113 _27742 h' t') = (term114 _27742 t').
Proof. exact (@lem1188957 _27742 h' t'). Qed.
Lemma lem1188959 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 t')) : ((term149 _27740 _27742 _27753 f h t h' t') = (term113 _27742 h' t')) = ((term114 _27742 t') = (term114 _27742 t')).
Proof. exact (MK_COMB (@lem1188954 _27740 _27742 _27753 h h' f t t' h1 h2) (@lem1188958 _27742 h' t')). Qed.
Lemma lem1188961 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1188817 m n) (@lem1188816 m n)). Qed.
Lemma lem1188962 {_27742 : Type'} (t' : list _27742) : ((term114 _27742 t') = (term114 _27742 t')) = ((@List.length _27742 t') = (@List.length _27742 t')).
Proof. exact (@lem1188961 (@List.length _27742 t') (@List.length _27742 t')). Qed.
Lemma lem1188964 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1188965 (x : nat) : (x = x) = True.
Proof. exact (@lem1188964 nat x). Qed.
Lemma lem1188966 {_27742 : Type'} (t' : list _27742) : ((@List.length _27742 t') = (@List.length _27742 t')) = True.
Proof. exact (@lem1188965 (@List.length _27742 t')). Qed.
Lemma lem1188967 {_27742 : Type'} (t' : list _27742) : ((term114 _27742 t') = (term114 _27742 t')) = True.
Proof. exact (TRANS (@lem1188962 _27742 t') (@lem1188966 _27742 t')). Qed.
Lemma lem1188968 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (t' : list _27742) (h1 : term8 _27740 _27742 _27753 f t) (h2 : (@List.length _27740 t) = (@List.length _27742 t')) : ((term149 _27740 _27742 _27753 f h t h' t') = (term113 _27742 h' t')) = True.
Proof. exact (TRANS (@lem1188959 _27740 _27742 _27753 h h' f t t' h1 h2) (@lem1188967 _27742 t')). Qed.
Lemma lem1188969 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (t' : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term164 _27740 _27742 _27753 f h t h' t'.
Proof. exact (fun h0 : (@List.length _27740 t) = (@List.length _27742 t') => @lem1188968 _27740 _27742 _27753 h h' f t t' h1 h0). Qed.
Lemma lem1188970 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (h' : _27742) (t : list _27740) (t' : list _27742) : term165 _27740 _27742 _27753 f h h' t t'.
Proof. exact (@lem1188915 _27740 _27742 _27753 f h h' t t' True). Qed.
Lemma lem1188971 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (t' : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : (term71 _27740 _27742 _27753 f h t h' t') = (term166 _27740 _27742 t t').
Proof. exact (@lem1188970 _27740 _27742 _27753 f h h' t t' (@lem1188969 _27740 _27742 _27753 h h' t' f t h1)). Qed.
Lemma lem1188975 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1188976 {_27740 _27742 : Type'} (t : list _27740) (t' : list _27742) : (term166 _27740 _27742 t t') = True.
Proof. exact (@lem1188975 ((@List.length _27740 t) = (@List.length _27742 t'))). Qed.
Lemma lem1188977 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (t' : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : (term71 _27740 _27742 _27753 f h t h' t') = True.
Proof. exact (TRANS (@lem1188971 _27740 _27742 _27753 h h' t' f t h1) (@lem1188976 _27740 _27742 t t')). Qed.
Lemma lem1188978 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (t' : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : True = (term71 _27740 _27742 _27753 f h t h' t').
Proof. exact (SYM (@lem1188977 _27740 _27742 _27753 h h' t' f t h1)). Qed.
Lemma lem1188979 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (t' : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term71 _27740 _27742 _27753 f h t h' t'.
Proof. exact (EQ_MP (@lem1188978 _27740 _27742 _27753 h h' t' f t h1) (@lem0)). Qed.
Lemma lem1188980 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (t' : list _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term73 _27740 _27742 _27753 f h t h' t'.
Proof. exact (fun h0 : term67 _27740 _27742 _27753 f h t t' => @lem1188979 _27740 _27742 _27753 h h' t' f t h1). Qed.
Lemma lem1188985 {_27740 _27742 _27753 : Type'} (h : _27740) (h' : _27742) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term77 _27740 _27742 _27753 f h t h'.
Proof. exact (fun t' : list _27742 => @lem1188980 _27740 _27742 _27753 h h' t' f t h1). Qed.
Lemma lem1188990 {_27740 _27742 _27753 : Type'} (h : _27740) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term81 _27740 _27742 _27753 f h t.
Proof. exact (fun h' : _27742 => @lem1188985 _27740 _27742 _27753 h h' f t h1). Qed.
Lemma lem1188991 {_27740 _27742 _27753 : Type'} (h : _27740) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term83 _27740 _27742 _27753 f h t.
Proof. exact (conj (@lem1188812 _27740 _27742 _27753 f h t) (@lem1188990 _27740 _27742 _27753 h f t h1)). Qed.
Lemma lem1188992 {_27740 _27742 _27753 : Type'} (h : _27740) (f : type1412 _27740 _27742 _27753) (t : list _27740) (h1 : term8 _27740 _27742 _27753 f t) : term12 _27740 _27742 _27753 f h t.
Proof. exact (@lem1188464 _27740 _27742 _27753 f h t (@lem1188991 _27740 _27742 _27753 h f t h1)). Qed.
Lemma lem1188993 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) (t : list _27742) : term44 _27740 _27742 _27753 f h t.
Proof. exact (fun h0 : term38 _27740 _27742 _27753 f t => @lem1188698 _27740 _27742 _27753 f h t). Qed.
Lemma lem1188998 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27742) : term48 _27740 _27742 _27753 f h.
Proof. exact (fun t : list _27742 => @lem1188993 _27740 _27742 _27753 f h t). Qed.
Lemma lem1189003 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term52 _27740 _27742 _27753 f.
Proof. exact (fun h : _27742 => @lem1188998 _27740 _27742 _27753 f h). Qed.
Lemma lem1189004 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term54 _27740 _27742 _27753 f.
Proof. exact (conj (@lem1188587 _27740 _27742 _27753 f) (@lem1189003 _27740 _27742 _27753 f)). Qed.
Lemma lem1189005 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term4 _27740 _27742 _27753 f.
Proof. exact (@lem1188436 _27740 _27742 _27753 f (@lem1189004 _27740 _27742 _27753 f)). Qed.
Lemma lem1189006 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) (t : list _27740) : term14 _27740 _27742 _27753 f h t.
Proof. exact (fun h0 : term8 _27740 _27742 _27753 f t => @lem1188992 _27740 _27742 _27753 h f t h0). Qed.
Lemma lem1189011 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) (h : _27740) : term18 _27740 _27742 _27753 f h.
Proof. exact (fun t : list _27740 => @lem1189006 _27740 _27742 _27753 f h t). Qed.
Lemma lem1189016 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term22 _27740 _27742 _27753 f.
Proof. exact (fun h : _27740 => @lem1189011 _27740 _27742 _27753 f h). Qed.
Lemma lem1189017 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term24 _27740 _27742 _27753 f.
Proof. exact (conj (@lem1189005 _27740 _27742 _27753 f) (@lem1189016 _27740 _27742 _27753 f)). Qed.
Lemma lem1189018 {_27740 _27742 _27753 : Type'} (f : type1412 _27740 _27742 _27753) : term29 _27740 _27742 _27753 f.
Proof. exact (@lem1188408 _27740 _27742 _27753 f (@lem1189017 _27740 _27742 _27753 f)). Qed.
Lemma lem1189023 {_27740 _27742 _27753 : Type'} : term167 _27740 _27742 _27753.
Proof. exact (fun f : type1412 _27740 _27742 _27753 => @lem1189018 _27740 _27742 _27753 f). Qed.
