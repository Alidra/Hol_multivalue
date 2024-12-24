Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_MOD_SELF_term_abbrevs.
Require Import INT_CONG_LREM_spec.
Require Import thm1032627_spec.
Require Import thm1032730_spec.
Require Import thm18392_spec.
Require Import thm2405764_spec.
Require Import thm2405813_spec.
Require Import thm2416517_spec.
Require Import thm2416521_spec.
Require Import thm2416523_spec.
Require Import thm2416525_spec.
Require Import thm2416531_spec.
Require Import thm2416533_spec.
Require Import thm2416549_spec.
Require Import thm2416594_spec.
Require Import thm2444030_spec.
Require Import thm2444031_spec.
Require Import thm2447306_spec.
Require Import thm2447307_spec.
Require Import thm62_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Require Import thm93_spec.
Lemma lem2528301 (x : int) : term0 x.
Proof. exact (@lem2528201 x). Qed.
Lemma lem2528302 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2528303 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2528302 x) (@lem2528301 x)). Qed.
Lemma lem2528304 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2528303 x y). Qed.
Lemma lem2528305 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2528306 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2528305 x y) (@lem2528304 x y)). Qed.
Lemma lem2528307 (x : int) (y : int) (n : int) : term4 x y n.
Proof. exact (@lem2528306 x y n). Qed.
Lemma lem2528308 (x : int) (y : int) (n : int) : (term4 x y n) = ((term5 x y n) = (term6 x y n)).
Proof. exact (eq_refl (term4 x y n)). Qed.
Lemma lem2528319 (x : int) (y : int) (n : int) : (term5 x y n) = (term6 x y n).
Proof. exact (EQ_MP (@lem2528308 x y n) (@lem2528307 x y n)). Qed.
Lemma lem2528320 (m : int) (n : int) : (term7 m n) = (term8 m n).
Proof. exact (@lem2528319 m m n). Qed.
Lemma lem2528321 (m : int) : (term9 m) = (term10 m).
Proof. exact (fun_ext (fun n : int => @lem2528320 m n)). Qed.
Lemma lem2528322 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528323 (m : int) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem2528322) (@lem2528321 m)). Qed.
Lemma lem2528328 : term13 = term14.
Proof. exact (fun_ext (fun m : int => @lem2528323 m)). Qed.
Lemma lem2528329 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528330 : term15 = term16.
Proof. exact (MK_COMB (@lem2528329) (@lem2528328)). Qed.
Lemma lem2528335 : term16 = term15.
Proof. exact (SYM (@lem2528330)). Qed.
Lemma lem2528345 (x : int) (y : int) (n : int) : (term6 x y n) = (term17 x y n).
Proof. exact (EQ_MP (@lem2447307 x y n) (@lem2447306 x y n)). Qed.
Lemma lem2528346 (m : int) (n : int) : (term8 m n) = (term18 m n).
Proof. exact (@lem2528345 m m n). Qed.
Lemma lem2528353 (m : int) : (term10 m) = (term19 m).
Proof. exact (fun_ext (fun n : int => @lem2528346 m n)). Qed.
Lemma lem2528354 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528355 (m : int) : (term12 m) = (term20 m).
Proof. exact (MK_COMB (@lem2528354) (@lem2528353 m)). Qed.
Lemma lem2528360 : term14 = term21.
Proof. exact (fun_ext (fun m : int => @lem2528355 m)). Qed.
Lemma lem2528361 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528362 : term16 = term22.
Proof. exact (MK_COMB (@lem2528361) (@lem2528360)). Qed.
Lemma lem2528367 : term22 = term16.
Proof. exact (SYM (@lem2528362)). Qed.
Lemma lem2528493 (x : int) (y : int) : (x = y) = ((int_sub x y) = term23).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem2528494 (m : int) (n : int) (d : int) : ((int_sub m m) = (int_mul n d)) = ((term24 m n d) = term23).
Proof. exact (@lem2528493 (int_sub m m) (int_mul n d)). Qed.
Lemma lem2528501 (d : int) (n : int) : (int_mul n d) = (int_mul d n).
Proof. exact (@lem2416549 d n). Qed.
Lemma lem2528507 (m : int) : (int_sub m m) = (term25 m).
Proof. exact (@lem2416594 m m). Qed.
Lemma lem2528511 (m : int) : (term25 m) = (term26 m).
Proof. exact (@lem2416517 term27 m). Qed.
Lemma lem2528513 (m : nat) : (term28 m) = term23.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem2528514 : term29 = term23.
Proof. exact (@lem2528513 term30). Qed.
Lemma lem2528515 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2528516 : term31 = term32.
Proof. exact (MK_COMB (@lem2528515) (@lem2528514)). Qed.
Lemma lem2528517 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2528518 (m : int) : (term26 m) = (term33 m).
Proof. exact (MK_COMB (@lem2528516) (@lem2528517 m)). Qed.
Lemma lem2528519 (m : int) : (term25 m) = (term33 m).
Proof. exact (TRANS (@lem2528511 m) (@lem2528518 m)). Qed.
Lemma lem2528520 (m : int) : (term33 m) = term23.
Proof. exact (@lem2416521 m). Qed.
Lemma lem2528522 (m : int) : (term25 m) = term23.
Proof. exact (TRANS (@lem2528519 m) (@lem2528520 m)). Qed.
Lemma lem2528524 (m : int) : (int_sub m m) = term23.
Proof. exact (TRANS (@lem2528507 m) (@lem2528522 m)). Qed.
Lemma lem2528525 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem2528526 (m : int) : (term34 m) = term35.
Proof. exact (MK_COMB (@lem2528525) (@lem2528524 m)). Qed.
Lemma lem2528527 (m : int) (d : int) (n : int) : (term24 m n d) = (term36 d n).
Proof. exact (MK_COMB (@lem2528526 m) (@lem2528501 d n)). Qed.
Lemma lem2528528 (d : int) (n : int) : (term36 d n) = (term37 d n).
Proof. exact (@lem2416594 term23 (int_mul d n)). Qed.
Lemma lem2528533 (d : int) (n : int) : (term37 d n) = (term38 d n).
Proof. exact (@lem2416523 (term38 d n)). Qed.
Lemma lem2528534 (d : int) (n : int) : (term36 d n) = (term38 d n).
Proof. exact (TRANS (@lem2528528 d n) (@lem2528533 d n)). Qed.
Lemma lem2528535 (m : int) (d : int) (n : int) : (term24 m n d) = (term38 d n).
Proof. exact (TRANS (@lem2528527 m d n) (@lem2528534 d n)). Qed.
Lemma lem2528536 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2528537 (m : int) (d : int) (n : int) : (term39 m n d) = (term40 d n).
Proof. exact (MK_COMB (@lem2528536) (@lem2528535 m d n)). Qed.
Lemma lem2528538 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem2528539 (m : int) (d : int) (n : int) : ((term24 m n d) = term23) = ((term38 d n) = term23).
Proof. exact (MK_COMB (@lem2528537 m d n) (@lem2528538)). Qed.
Lemma lem2528540 (m : int) (d : int) (n : int) : ((int_sub m m) = (int_mul n d)) = ((term38 d n) = term23).
Proof. exact (TRANS (@lem2528494 m n d) (@lem2528539 m d n)). Qed.
Lemma lem2528541 (m : int) (n : int) : (term41 m n) = (term42 n).
Proof. exact (fun_ext (fun d : int => @lem2528540 m d n)). Qed.
Lemma lem2528542 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2528543 (m : int) (n : int) : (term18 m n) = (term43 n).
Proof. exact (MK_COMB (@lem2528542) (@lem2528541 m n)). Qed.
Lemma lem2528544 (m : int) (n : int) : (term43 n) = (term18 m n).
Proof. exact (SYM (@lem2528543 m n)). Qed.
Lemma lem2528556 (_29815 : int) (n : int) : ((term38 _29815 n) = term23) = ((term38 _29815 n) = term23).
Proof. exact (eq_refl ((term38 _29815 n) = term23)). Qed.
Lemma lem2528557 (n : int) : (term42 n) = (term42 n).
Proof. exact (fun_ext (fun _29815 : int => @lem2528556 _29815 n)). Qed.
Lemma lem2528558 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2528560 (n : int) : (term43 n) = (term43 n).
Proof. exact (MK_COMB (@lem2528558) (@lem2528557 n)). Qed.
Lemma lem2528561 (n : int) : (term43 n) = (term43 n).
Proof. exact (SYM (@lem2528560 n)). Qed.
Lemma lem2528563 (x : int) (y : int) : (x = y) = ((int_sub x y) = term23).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem2528564 (_29815 : int) (n : int) : ((term38 _29815 n) = term23) = ((term44 _29815 n) = term23).
Proof. exact (@lem2528563 (term38 _29815 n) term23). Qed.
Lemma lem2528582 (_29815 : int) (n : int) : (term44 _29815 n) = (term45 _29815 n).
Proof. exact (@lem2416594 (term38 _29815 n) term23). Qed.
Lemma lem2528584 (x : nat) : (term46 x) = term23.
Proof. exact (proj2 (@lem2405764 x)). Qed.
Lemma lem2528585 : term47 = term23.
Proof. exact (@lem2528584 term30). Qed.
Lemma lem2528586 (_29815 : int) (n : int) : (term48 _29815 n) = (term48 _29815 n).
Proof. exact (eq_refl (term48 _29815 n)). Qed.
Lemma lem2528587 (_29815 : int) (n : int) : (term45 _29815 n) = (term49 _29815 n).
Proof. exact (MK_COMB (@lem2528586 _29815 n) (@lem2528585)). Qed.
Lemma lem2528588 (_29815 : int) (n : int) : (term49 _29815 n) = (term38 _29815 n).
Proof. exact (@lem2416525 (term38 _29815 n)). Qed.
Lemma lem2528589 (_29815 : int) (n : int) : (term45 _29815 n) = (term38 _29815 n).
Proof. exact (TRANS (@lem2528587 _29815 n) (@lem2528588 _29815 n)). Qed.
Lemma lem2528591 (_29815 : int) (n : int) : (term44 _29815 n) = (term38 _29815 n).
Proof. exact (TRANS (@lem2528582 _29815 n) (@lem2528589 _29815 n)). Qed.
Lemma lem2528592 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2528593 (_29815 : int) (n : int) : (term50 _29815 n) = (term40 _29815 n).
Proof. exact (MK_COMB (@lem2528592) (@lem2528591 _29815 n)). Qed.
Lemma lem2528594 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem2528595 (_29815 : int) (n : int) : ((term44 _29815 n) = term23) = ((term38 _29815 n) = term23).
Proof. exact (MK_COMB (@lem2528593 _29815 n) (@lem2528594)). Qed.
Lemma lem2528596 (_29815 : int) (n : int) : ((term38 _29815 n) = term23) = ((term38 _29815 n) = term23).
Proof. exact (TRANS (@lem2528564 _29815 n) (@lem2528595 _29815 n)). Qed.
Lemma lem2528597 (n : int) : (term42 n) = (term42 n).
Proof. exact (fun_ext (fun _29815 : int => @lem2528596 _29815 n)). Qed.
Lemma lem2528598 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2528599 (n : int) : (term43 n) = (term43 n).
Proof. exact (MK_COMB (@lem2528598) (@lem2528597 n)). Qed.
Lemma lem2528600 (n : int) : (term43 n) = (term43 n).
Proof. exact (SYM (@lem2528599 n)). Qed.
Lemma lem2528608 (n : int) : ((term51 n) = term23) = ((term51 n) = term23).
Proof. exact (eq_refl ((term51 n) = term23)). Qed.
Lemma lem2528609 : term52 = term52.
Proof. exact (fun_ext (fun n : int => @lem2528608 n)). Qed.
Lemma lem2528610 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528611 : term53 = term53.
Proof. exact (MK_COMB (@lem2528610) (@lem2528609)). Qed.
Lemma lem2528612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2528614 : term54 = term54.
Proof. exact (MK_COMB (@lem2528612) (@lem2528611)). Qed.
Lemma lem2528616 (P : int -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2528617 : term54 = term57.
Proof. exact (@lem2528616 term52). Qed.
Lemma lem2528618 (n : int) : (term58 n) = ((term51 n) = term23).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem2528619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2528621 (n : int) : (term59 n) = (term60 n).
Proof. exact (MK_COMB (@lem2528619) (@lem2528618 n)). Qed.
Lemma lem2528622 : term61 = term62.
Proof. exact (fun_ext (fun n : int => @lem2528621 n)). Qed.
Lemma lem2528623 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2528624 : term57 = term63.
Proof. exact (MK_COMB (@lem2528623) (@lem2528622)). Qed.
Lemma lem2528625 : term54 = term63.
Proof. exact (TRANS (@lem2528617) (@lem2528624)). Qed.
Lemma lem2528630 : term54 = term63.
Proof. exact (TRANS (@lem2528614) (@lem2528625)). Qed.
Lemma lem2528632 (n : int) (h1 : term60 n) : term60 n.
Proof. exact (h1). Qed.
Lemma lem2528633 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem2528640 (n : int) : (term33 n) = term23.
Proof. exact (@lem2416531 n). Qed.
Lemma lem2528643 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem2528644 (n : int) : (term51 n) = term47.
Proof. exact (MK_COMB (@lem2528643) (@lem2528640 n)). Qed.
Lemma lem2528645 : term47 = term23.
Proof. exact (@lem2416533 term27). Qed.
Lemma lem2528646 (n : int) : (term51 n) = term23.
Proof. exact (TRANS (@lem2528644 n) (@lem2528645)). Qed.
Lemma lem2528647 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2528648 (n : int) : (term65 n) = term66.
Proof. exact (MK_COMB (@lem2528647) (@lem2528646 n)). Qed.
Lemma lem2528649 (n : int) : ((term51 n) = term23) = (term23 = term23).
Proof. exact (MK_COMB (@lem2528648 n) (@lem2528633)). Qed.
Lemma lem2528650 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2528651 (n : int) : (term60 n) = term67.
Proof. exact (MK_COMB (@lem2528650) (@lem2528649 n)). Qed.
Lemma lem2528652 (n : int) (h1 : term60 n) : term67.
Proof. exact (EQ_MP (@lem2528651 n) (@lem2528632 n h1)). Qed.
Lemma lem2528653 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem2528654 : term68.
Proof. exact (@lem82 (term23 = term23)). Qed.
Lemma lem2528655 (n : int) (h1 : term60 n) : (term23 = term23) = False.
Proof. exact (@lem2528654 (@lem2528652 n h1)). Qed.
Lemma lem2528656 (n : int) (h1 : term60 n) : False.
Proof. exact (EQ_MP (@lem2528655 n h1) (@lem2528653)). Qed.
Lemma lem2528657 (n : int) : term69 n.
Proof. exact (fun h0 : term60 n => @lem2528656 n h0). Qed.
Lemma lem2528658 (n : int) : (term69 n) = (term70 n).
Proof. exact (@lem69 (term60 n)). Qed.
Lemma lem2528659 (n : int) : term70 n.
Proof. exact (EQ_MP (@lem2528658 n) (@lem2528657 n)). Qed.
Lemma lem2528660 (n : int) : term71 n.
Proof. exact (@lem82 (term60 n)). Qed.
Lemma lem2528662 (n : int) : (term60 n) = False.
Proof. exact (@lem2528660 n (@lem2528659 n)). Qed.
Lemma lem2528663 (n : int) : term72 n.
Proof. exact (@lem93 (term60 n)). Qed.
Lemma lem2528664 (n : int) : term70 n.
Proof. exact (@lem2528663 n (@lem2528662 n)). Qed.
Lemma lem2528665 (n : int) : (term70 n) = (term69 n).
Proof. exact (@lem62 (term60 n)). Qed.
Lemma lem2528666 (n : int) : term69 n.
Proof. exact (EQ_MP (@lem2528665 n) (@lem2528664 n)). Qed.
Lemma lem2528667 (n : int) (h1 : term60 n) : term60 n.
Proof. exact (h1). Qed.
Lemma lem2528668 (n : int) (h1 : term60 n) : False.
Proof. exact (@lem2528666 n (@lem2528667 n h1)). Qed.
Lemma lem2528669 (h1 : term63) : term63.
Proof. exact (h1). Qed.
Lemma lem2528670 (h1 : term63) : False.
Proof. exact (ex_elim (@lem2528669 h1) (fun n : int => fun h0 : term62 n => @lem2528668 n h0)). Qed.
Lemma lem2528671 : term73.
Proof. exact (fun h0 : term63 => @lem2528670 h0). Qed.
Lemma lem2528673 (p : Prop) (q : Prop) : term74 p q.
Proof. exact (EQ_MP (@lem1032627 p q) (@lem1032730 p q)). Qed.
Lemma lem2528674 (q : Prop) : term75 q.
Proof. exact (@lem2528673 term63 q). Qed.
Lemma lem2528677 (q : Prop) : term76 q.
Proof. exact (@lem2528674 q (@lem2528671)). Qed.
Lemma lem2528678 : term77.
Proof. exact (@lem2528677 term53). Qed.
Lemma lem2528679 : term53.
Proof. exact (@lem2528678 (@lem2528630)). Qed.
Lemma lem2528680 (n : int) : term58 n.
Proof. exact (@lem2528679 n). Qed.
Lemma lem2528681 (n : int) : (term58 n) = ((term51 n) = term23).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem2528682 (n : int) : (term51 n) = term23.
Proof. exact (EQ_MP (@lem2528681 n) (@lem2528680 n)). Qed.
Lemma lem2528683 (n : int) : term43 n.
Proof. exact (ex_intro (term42 n) term23 (@lem2528682 n)). Qed.
Lemma lem2528684 (n : int) : term43 n.
Proof. exact (EQ_MP (@lem2528600 n) (@lem2528683 n)). Qed.
Lemma lem2528686 (n : int) : term43 n.
Proof. exact (EQ_MP (@lem2528561 n) (@lem2528684 n)). Qed.
Lemma lem2528690 (m : int) (n : int) : term18 m n.
Proof. exact (EQ_MP (@lem2528544 m n) (@lem2528686 n)). Qed.
Lemma lem2528695 (m : int) : term20 m.
Proof. exact (fun n : int => @lem2528690 m n). Qed.
Lemma lem2528700 : term22.
Proof. exact (fun m : int => @lem2528695 m). Qed.
Lemma lem2528701 : term16.
Proof. exact (EQ_MP (@lem2528367) (@lem2528700)). Qed.
Lemma lem2528702 : term15.
Proof. exact (EQ_MP (@lem2528335) (@lem2528701)). Qed.
