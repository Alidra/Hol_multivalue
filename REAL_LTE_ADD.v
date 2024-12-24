Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LTE_ADD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_ADD_RID_spec.
Require Import REAL_LTE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339889_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1379423 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1379424 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1379425 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1379424 t1) (@lem1379423 t1)). Qed.
Lemma lem1379426 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1379425 t1 t2). Qed.
Lemma lem1379427 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1379428 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1379427 t1 t2) (@lem1379426 t1 t2)). Qed.
Lemma lem1379429 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1379428 t1 t2 t3). Qed.
Lemma lem1379430 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1379431 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1379430 t1 t2 t3) (@lem1379429 t1 t2 t3)). Qed.
Lemma lem1379432 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1379431 t1 t2 t3)). Qed.
Lemma lem1379434 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1379435 : term8 = term9.
Proof. exact (@lem1379434 term8). Qed.
Lemma lem1379436 : term9 = term8.
Proof. exact (SYM (@lem1379435)). Qed.
Lemma lem1379437 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1379440 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1379441 : term12.
Proof. exact (fun h0 : term11 => @lem1379440 h0). Qed.
Lemma lem1379442 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1379443 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1379444 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1379442 h2 (@lem1379443 h1)). Qed.
Lemma lem1379445 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1379444 h1 h0). Qed.
Lemma lem1379446 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1379447 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1379445 h1 (@lem1379446 h2)). Qed.
Lemma lem1379448 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1379447 h0 h1). Qed.
Lemma lem1379449 : term14.
Proof. exact (fun h0 : term12 => @lem1379448 h0). Qed.
Lemma lem1379452 : term12.
Proof. exact (@lem1379449 (@lem1379441)). Qed.
Lemma lem1379492 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1379493 : term15 = term16.
Proof. exact (@lem1379492 term17). Qed.
Lemma lem1379508 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1379509 : term19 = term20.
Proof. exact (MK_COMB (@lem1379508) (@lem1379493)). Qed.
Lemma lem1379512 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1379513 : term22 = term23.
Proof. exact (MK_COMB (@lem1379512) (@lem1379509)). Qed.
Lemma lem1379516 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1379523 : term11 = term25.
Proof. exact (MK_COMB (@lem1379516) (@lem1379513)). Qed.
Lemma lem1379528 (y : real) (x : real) (z : real) : (term26 y x z) = (term26 y x z).
Proof. exact (eq_refl (term26 y x z)). Qed.
Lemma lem1379529 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (fun_ext (fun z : real => @lem1379528 y x z)). Qed.
Lemma lem1379530 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379531 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (MK_COMB (@lem1379530) (@lem1379529 y x)). Qed.
Lemma lem1379532 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1379531 y x)). Qed.
Lemma lem1379533 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379534 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1379533) (@lem1379532 x)). Qed.
Lemma lem1379535 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1379534 x)). Qed.
Lemma lem1379536 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379537 : term17 = term17.
Proof. exact (MK_COMB (@lem1379536) (@lem1379535)). Qed.
Lemma lem1379538 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1379539 : term16 = term16.
Proof. exact (MK_COMB (@lem1379538) (@lem1379537)). Qed.
Lemma lem1379540 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1379541 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1379540 x)). Qed.
Lemma lem1379542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379543 : term34 = term34.
Proof. exact (MK_COMB (@lem1379542) (@lem1379541)). Qed.
Lemma lem1379544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1379545 : term18 = term18.
Proof. exact (MK_COMB (@lem1379544) (@lem1379543)). Qed.
Lemma lem1379546 : term20 = term20.
Proof. exact (MK_COMB (@lem1379545) (@lem1379539)). Qed.
Lemma lem1379555 (y : real) (x : real) (z : real) : (term35 y x z) = (term35 y x z).
Proof. exact (eq_refl (term35 y x z)). Qed.
Lemma lem1379556 (y : real) (x : real) : (term36 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1379555 y x z)). Qed.
Lemma lem1379557 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379558 (y : real) (x : real) : (term37 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1379557) (@lem1379556 y x)). Qed.
Lemma lem1379559 (x : real) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1379558 y x)). Qed.
Lemma lem1379560 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379561 (x : real) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1379560) (@lem1379559 x)). Qed.
Lemma lem1379562 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1379561 x)). Qed.
Lemma lem1379563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379564 : term41 = term41.
Proof. exact (MK_COMB (@lem1379563) (@lem1379562)). Qed.
Lemma lem1379565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1379566 : term21 = term21.
Proof. exact (MK_COMB (@lem1379565) (@lem1379564)). Qed.
Lemma lem1379567 : term23 = term23.
Proof. exact (MK_COMB (@lem1379566) (@lem1379546)). Qed.
Lemma lem1379576 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1379577 (x : real) : (term43 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1379576 x y)). Qed.
Lemma lem1379578 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379579 (x : real) : (term44 x) = (term44 x).
Proof. exact (MK_COMB (@lem1379578) (@lem1379577 x)). Qed.
Lemma lem1379580 : term45 = term45.
Proof. exact (fun_ext (fun x : real => @lem1379579 x)). Qed.
Lemma lem1379581 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379582 : term8 = term8.
Proof. exact (MK_COMB (@lem1379581) (@lem1379580)). Qed.
Lemma lem1379583 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1379584 : term10 = term10.
Proof. exact (MK_COMB (@lem1379583) (@lem1379582)). Qed.
Lemma lem1379585 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1379586 : term24 = term24.
Proof. exact (MK_COMB (@lem1379585) (@lem1379584)). Qed.
Lemma lem1379587 : term25 = term25.
Proof. exact (MK_COMB (@lem1379586) (@lem1379567)). Qed.
Lemma lem1379660 : term11 = term25.
Proof. exact (TRANS (@lem1379523) (@lem1379587)). Qed.
Lemma lem1379661 : term25 = term11.
Proof. exact (SYM (@lem1379660)). Qed.
Lemma lem1379662 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1379663 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1379664 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1379665 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1379676 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (@lem17362 (term48 x y) (term49 x y)). Qed.
Lemma lem1379677 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1379678 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1379677 (term43 x)). Qed.
Lemma lem1379679 (x : real) (y : real) : (term54 x y) = (term42 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1379680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1379681 (x : real) (y : real) : (term55 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1379680) (@lem1379679 x y)). Qed.
Lemma lem1379682 (x : real) (y : real) : (term55 x y) = (term47 x y).
Proof. exact (TRANS (@lem1379681 x y) (@lem1379676 x y)). Qed.
Lemma lem1379683 (x : real) : (term56 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1379682 x y)). Qed.
Lemma lem1379684 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1379685 (x : real) : (term53 x) = (term58 x).
Proof. exact (MK_COMB (@lem1379684) (@lem1379683 x)). Qed.
Lemma lem1379686 (x : real) : (term52 x) = (term58 x).
Proof. exact (TRANS (@lem1379678 x) (@lem1379685 x)). Qed.
Lemma lem1379687 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1379688 : term10 = term59.
Proof. exact (@lem1379687 term45). Qed.
Lemma lem1379689 (x : real) : (term60 x) = (term44 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1379690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1379691 (x : real) : (term61 x) = (term52 x).
Proof. exact (MK_COMB (@lem1379690) (@lem1379689 x)). Qed.
Lemma lem1379692 (x : real) : (term61 x) = (term58 x).
Proof. exact (TRANS (@lem1379691 x) (@lem1379686 x)). Qed.
Lemma lem1379693 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1379692 x)). Qed.
Lemma lem1379694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1379695 : term59 = term64.
Proof. exact (MK_COMB (@lem1379694) (@lem1379693)). Qed.
Lemma lem1379752 : term10 = term64.
Proof. exact (TRANS (@lem1379688) (@lem1379695)). Qed.
Lemma lem1379753 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1379752) (@lem1379662 h1)). Qed.
Lemma lem1379760 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem17045 (real_lt x y) (real_le y z)). Qed.
Lemma lem1379761 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem1379762 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1379763 (x : real) (y : real) (z : real) : (term67 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1379762) (@lem1379760 x y z)). Qed.
Lemma lem1379764 (y : real) (x : real) (z : real) : (term69 y x z) = (term70 y x z).
Proof. exact (MK_COMB (@lem1379763 x y z) (@lem1379761 x z)). Qed.
Lemma lem1379765 (y : real) (x : real) (z : real) : (term35 y x z) = (term69 y x z).
Proof. exact (@lem17265 (term71 x y z) (real_lt x z)). Qed.
Lemma lem1379766 (y : real) (x : real) (z : real) : (term35 y x z) = (term70 y x z).
Proof. exact (TRANS (@lem1379765 y x z) (@lem1379764 y x z)). Qed.
Lemma lem1379767 (y : real) (x : real) : (term36 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1379766 y x z)). Qed.
Lemma lem1379768 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379769 (y : real) (x : real) : (term37 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1379768) (@lem1379767 y x)). Qed.
Lemma lem1379770 (x : real) : (term38 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1379769 y x)). Qed.
Lemma lem1379771 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379772 (x : real) : (term39 x) = (term75 x).
Proof. exact (MK_COMB (@lem1379771) (@lem1379770 x)). Qed.
Lemma lem1379773 : term40 = term76.
Proof. exact (fun_ext (fun x : real => @lem1379772 x)). Qed.
Lemma lem1379774 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379835 : term41 = term77.
Proof. exact (MK_COMB (@lem1379774) (@lem1379773)). Qed.
Lemma lem1379836 (h1 : term41) : term77.
Proof. exact (EQ_MP (@lem1379835) (@lem1379663 h1)). Qed.
Lemma lem1379837 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1379838 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1379837 x)). Qed.
Lemma lem1379839 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379848 : term34 = term34.
Proof. exact (MK_COMB (@lem1379839) (@lem1379838)). Qed.
Lemma lem1379849 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1379848) (@lem1379664 h1)). Qed.
Lemma lem1379856 (y : real) (x : real) (z : real) : (term26 y x z) = (term78 y x z).
Proof. exact (@lem17265 (real_le y z) (term79 y x z)). Qed.
Lemma lem1379857 (y : real) (x : real) : (term27 y x) = (term80 y x).
Proof. exact (fun_ext (fun z : real => @lem1379856 y x z)). Qed.
Lemma lem1379858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379859 (y : real) (x : real) : (term28 y x) = (term81 y x).
Proof. exact (MK_COMB (@lem1379858) (@lem1379857 y x)). Qed.
Lemma lem1379860 (x : real) : (term29 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1379859 y x)). Qed.
Lemma lem1379861 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379862 (x : real) : (term30 x) = (term83 x).
Proof. exact (MK_COMB (@lem1379861) (@lem1379860 x)). Qed.
Lemma lem1379863 : term31 = term84.
Proof. exact (fun_ext (fun x : real => @lem1379862 x)). Qed.
Lemma lem1379864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379925 : term17 = term85.
Proof. exact (MK_COMB (@lem1379864) (@lem1379863)). Qed.
Lemma lem1379926 (h1 : term17) : term85.
Proof. exact (EQ_MP (@lem1379925) (@lem1379665 h1)). Qed.
Lemma lem1379927 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1379953 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1379954 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1379953 y x z)). Qed.
Lemma lem1379955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379956 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1379955) (@lem1379954 y x)). Qed.
Lemma lem1379957 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1379956 y x)). Qed.
Lemma lem1379958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379959 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1379958) (@lem1379957 x)). Qed.
Lemma lem1379960 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1379959 x)). Qed.
Lemma lem1379961 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379962 : term77 = term77.
Proof. exact (MK_COMB (@lem1379961) (@lem1379960)). Qed.
Lemma lem1379963 (h1 : term41) : term77.
Proof. exact (EQ_MP (@lem1379962) (@lem1379836 h1)). Qed.
Lemma lem1379976 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1379977 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1379976 x)). Qed.
Lemma lem1379978 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379979 : term34 = term34.
Proof. exact (MK_COMB (@lem1379978) (@lem1379977)). Qed.
Lemma lem1379980 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1379979) (@lem1379849 h1)). Qed.
Lemma lem1380003 (y : real) (x : real) (z : real) : (term78 y x z) = (term78 y x z).
Proof. exact (eq_refl (term78 y x z)). Qed.
Lemma lem1380004 (y : real) (x : real) : (term80 y x) = (term80 y x).
Proof. exact (fun_ext (fun z : real => @lem1380003 y x z)). Qed.
Lemma lem1380005 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380006 (y : real) (x : real) : (term81 y x) = (term81 y x).
Proof. exact (MK_COMB (@lem1380005) (@lem1380004 y x)). Qed.
Lemma lem1380007 (x : real) : (term82 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1380006 y x)). Qed.
Lemma lem1380008 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380009 (x : real) : (term83 x) = (term83 x).
Proof. exact (MK_COMB (@lem1380008) (@lem1380007 x)). Qed.
Lemma lem1380010 : term84 = term84.
Proof. exact (fun_ext (fun x : real => @lem1380009 x)). Qed.
Lemma lem1380011 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380012 : term85 = term85.
Proof. exact (MK_COMB (@lem1380011) (@lem1380010)). Qed.
Lemma lem1380013 (h1 : term17) : term85.
Proof. exact (EQ_MP (@lem1380012) (@lem1379926 h1)). Qed.
Lemma lem1380053 (x : real) (y : real) (h1 : term47 x y) : term47 x y.
Proof. exact (h1). Qed.
Lemma lem1380055 (x : real) (y : real) (h1 : term47 x y) : term48 x y.
Proof. exact (proj1 (@lem1380053 x y h1)). Qed.
Lemma lem1380071 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1380072 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1380071 y x z)). Qed.
Lemma lem1380073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380074 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1380073) (@lem1380072 y x)). Qed.
Lemma lem1380075 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1380074 y x)). Qed.
Lemma lem1380076 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380077 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1380076) (@lem1380075 x)). Qed.
Lemma lem1380078 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1380077 x)). Qed.
Lemma lem1380079 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380081 : term77 = term77.
Proof. exact (MK_COMB (@lem1380079) (@lem1380078)). Qed.
Lemma lem1380082 (h1 : term41) : term77.
Proof. exact (EQ_MP (@lem1380081) (@lem1379963 h1)). Qed.
Lemma lem1380084 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1380085 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1380084 x)). Qed.
Lemma lem1380086 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380088 : term34 = term34.
Proof. exact (MK_COMB (@lem1380086) (@lem1380085)). Qed.
Lemma lem1380089 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1380088) (@lem1379980 h1)). Qed.
Lemma lem1380097 (y : real) (x : real) (z : real) : (term78 y x z) = (term78 y x z).
Proof. exact (eq_refl (term78 y x z)). Qed.
Lemma lem1380098 (y : real) (x : real) : (term80 y x) = (term80 y x).
Proof. exact (fun_ext (fun z : real => @lem1380097 y x z)). Qed.
Lemma lem1380099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380100 (y : real) (x : real) : (term81 y x) = (term81 y x).
Proof. exact (MK_COMB (@lem1380099) (@lem1380098 y x)). Qed.
Lemma lem1380101 (x : real) : (term82 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1380100 y x)). Qed.
Lemma lem1380102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380103 (x : real) : (term83 x) = (term83 x).
Proof. exact (MK_COMB (@lem1380102) (@lem1380101 x)). Qed.
Lemma lem1380104 : term84 = term84.
Proof. exact (fun_ext (fun x : real => @lem1380103 x)). Qed.
Lemma lem1380105 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1380107 : term85 = term85.
Proof. exact (MK_COMB (@lem1380105) (@lem1380104)). Qed.
Lemma lem1380108 (h1 : term17) : term85.
Proof. exact (EQ_MP (@lem1380107) (@lem1380013 h1)). Qed.
Lemma lem1380121 (_24448 : real) (h1 : term41) : term86 _24448.
Proof. exact (@lem1380082 h1 _24448). Qed.
Lemma lem1380122 (_24448 : real) : (term86 _24448) = (term75 _24448).
Proof. exact (eq_refl (term86 _24448)). Qed.
Lemma lem1380123 (_24448 : real) (h1 : term41) : term75 _24448.
Proof. exact (EQ_MP (@lem1380122 _24448) (@lem1380121 _24448 h1)). Qed.
Lemma lem1380124 (_24448 : real) (_24449 : real) (h1 : term41) : term87 _24448 _24449.
Proof. exact (@lem1380123 _24448 h1 _24449). Qed.
Lemma lem1380125 (_24449 : real) (_24448 : real) : (term87 _24448 _24449) = (term73 _24449 _24448).
Proof. exact (eq_refl (term87 _24448 _24449)). Qed.
Lemma lem1380126 (_24449 : real) (_24448 : real) (h1 : term41) : term73 _24449 _24448.
Proof. exact (EQ_MP (@lem1380125 _24449 _24448) (@lem1380124 _24448 _24449 h1)). Qed.
Lemma lem1380127 (_24449 : real) (_24448 : real) (_24450 : real) (h1 : term41) : term88 _24449 _24448 _24450.
Proof. exact (@lem1380126 _24449 _24448 h1 _24450). Qed.
Lemma lem1380128 (_24449 : real) (_24448 : real) (_24450 : real) : (term88 _24449 _24448 _24450) = (term70 _24449 _24448 _24450).
Proof. exact (eq_refl (term88 _24449 _24448 _24450)). Qed.
Lemma lem1380129 (_24449 : real) (_24448 : real) (_24450 : real) (h1 : term41) : term70 _24449 _24448 _24450.
Proof. exact (EQ_MP (@lem1380128 _24449 _24448 _24450) (@lem1380127 _24449 _24448 _24450 h1)). Qed.
Lemma lem1380130 (_24451 : real) (h1 : term34) : term89 _24451.
Proof. exact (@lem1380089 h1 _24451). Qed.
Lemma lem1380131 (_24451 : real) : (term89 _24451) = ((term32 _24451) = _24451).
Proof. exact (eq_refl (term89 _24451)). Qed.
Lemma lem1380133 (_24452 : real) (h1 : term17) : term90 _24452.
Proof. exact (@lem1380108 h1 _24452). Qed.
Lemma lem1380134 (_24452 : real) : (term90 _24452) = (term83 _24452).
Proof. exact (eq_refl (term90 _24452)). Qed.
Lemma lem1380135 (_24452 : real) (h1 : term17) : term83 _24452.
Proof. exact (EQ_MP (@lem1380134 _24452) (@lem1380133 _24452 h1)). Qed.
Lemma lem1380136 (_24452 : real) (_24453 : real) (h1 : term17) : term91 _24452 _24453.
Proof. exact (@lem1380135 _24452 h1 _24453). Qed.
Lemma lem1380137 (_24453 : real) (_24452 : real) : (term91 _24452 _24453) = (term81 _24453 _24452).
Proof. exact (eq_refl (term91 _24452 _24453)). Qed.
Lemma lem1380138 (_24453 : real) (_24452 : real) (h1 : term17) : term81 _24453 _24452.
Proof. exact (EQ_MP (@lem1380137 _24453 _24452) (@lem1380136 _24452 _24453 h1)). Qed.
Lemma lem1380139 (_24453 : real) (_24452 : real) (_24454 : real) (h1 : term17) : term92 _24453 _24452 _24454.
Proof. exact (@lem1380138 _24453 _24452 h1 _24454). Qed.
Lemma lem1380140 (_24453 : real) (_24452 : real) (_24454 : real) : (term92 _24453 _24452 _24454) = (term78 _24453 _24452 _24454).
Proof. exact (eq_refl (term92 _24453 _24452 _24454)). Qed.
Lemma lem1380152 (_24449 : real) (_24448 : real) (_24450 : real) : (term70 _24449 _24448 _24450) = (term93 _24449 _24448 _24450).
Proof. exact (@lem1379432 (term94 _24448 _24449) (term95 _24449 _24450) (real_lt _24448 _24450)). Qed.
Lemma lem1380153 (_24449 : real) (_24448 : real) (_24450 : real) (h1 : term41) : term93 _24449 _24448 _24450.
Proof. exact (EQ_MP (@lem1380152 _24449 _24448 _24450) (@lem1380129 _24449 _24448 _24450 h1)). Qed.
Lemma lem1380161 (_24453 : real) (_24452 : real) (_24454 : real) (h1 : term17) : term78 _24453 _24452 _24454.
Proof. exact (EQ_MP (@lem1380140 _24453 _24452 _24454) (@lem1380139 _24453 _24452 _24454 h1)). Qed.
Lemma lem1380163 (x : real) (y : real) (h1 : term47 x y) : term96 x y.
Proof. exact (proj2 (@lem1380053 x y h1)). Qed.
Lemma lem1380168 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1380169 (_24455 : real) (_24457 : real) (h1 : _24455 = _24457) : _24455 = _24457.
Proof. exact (h1). Qed.
Lemma lem1380170 (_24456 : real) (_24458 : real) (h1 : _24456 = _24458) : _24456 = _24458.
Proof. exact (h1). Qed.
Lemma lem1380171 (_24455 : real) (_24457 : real) (h1 : _24455 = _24457) : (real_le _24455) = (real_le _24457).
Proof. exact (MK_COMB (@lem1380168) (@lem1380169 _24455 _24457 h1)). Qed.
Lemma lem1380172 (_24455 : real) (_24457 : real) (_24456 : real) (_24458 : real) (h1 : _24455 = _24457) (h2 : _24456 = _24458) : (real_le _24455 _24456) = (real_le _24457 _24458).
Proof. exact (MK_COMB (@lem1380171 _24455 _24457 h1) (@lem1380170 _24456 _24458 h2)). Qed.
Lemma lem1380174 (b : Prop) (a : Prop) : term97 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1380175 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : term98 _24457 _24458 _24455 _24456.
Proof. exact (@lem1380174 (real_le _24457 _24458) (real_le _24455 _24456)). Qed.
Lemma lem1380176 (_24455 : real) (_24457 : real) (_24456 : real) (_24458 : real) (h1 : _24455 = _24457) (h2 : _24456 = _24458) : term99 _24457 _24458 _24455 _24456.
Proof. exact (@lem1380175 _24457 _24458 _24455 _24456 (@lem1380172 _24455 _24457 _24456 _24458 h1 h2)). Qed.
Lemma lem1380177 (_24458 : real) (_24456 : real) (_24455 : real) (_24457 : real) (h1 : _24455 = _24457) : term100 _24457 _24458 _24455 _24456.
Proof. exact (fun h0 : _24456 = _24458 => @lem1380176 _24455 _24457 _24456 _24458 h1 h0). Qed.
Lemma lem1380179 (a : Prop) (b : Prop) : (a -> b) = (term101 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1380180 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term100 _24457 _24458 _24455 _24456) = (term102 _24457 _24458 _24455 _24456).
Proof. exact (@lem1380179 (_24456 = _24458) (term99 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380181 (_24458 : real) (_24456 : real) (_24455 : real) (_24457 : real) (h1 : _24455 = _24457) : term102 _24457 _24458 _24455 _24456.
Proof. exact (EQ_MP (@lem1380180 _24457 _24458 _24455 _24456) (@lem1380177 _24458 _24456 _24455 _24457 h1)). Qed.
Lemma lem1380182 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : term103 _24457 _24458 _24455 _24456.
Proof. exact (fun h0 : _24455 = _24457 => @lem1380181 _24458 _24456 _24455 _24457 h0). Qed.
Lemma lem1380184 (a : Prop) (b : Prop) : (a -> b) = (term101 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1380185 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term103 _24457 _24458 _24455 _24456) = (term104 _24457 _24458 _24455 _24456).
Proof. exact (@lem1380184 (_24455 = _24457) (term102 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380186 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : term104 _24457 _24458 _24455 _24456.
Proof. exact (EQ_MP (@lem1380185 _24457 _24458 _24455 _24456) (@lem1380182 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380242 (x : real) (y : real) (h1 : term47 x y) : term105 x.
Proof. exact (proj1 (@lem1380055 x y h1)). Qed.
Lemma lem1380243 (x : real) (y : real) (h1 : term47 x y) : term106 x.
Proof. exact (fun h0 : term107 x => @lem1380242 x y h1). Qed.
Lemma lem1380245 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380246 (x : real) : (term106 x) = (term105 x).
Proof. exact (@lem1380245 (term105 x)). Qed.
Lemma lem1380247 (x : real) (y : real) (h1 : term47 x y) : term105 x.
Proof. exact (EQ_MP (@lem1380246 x) (@lem1380243 x y h1)). Qed.
Lemma lem1380249 (_24451 : real) (h1 : term34) : (term32 _24451) = _24451.
Proof. exact (EQ_MP (@lem1380131 _24451) (@lem1380130 _24451 h1)). Qed.
Lemma lem1380250 (x : real) (h1 : term34) : (term32 x) = x.
Proof. exact (@lem1380249 x h1). Qed.
Lemma lem1380251 (x : real) (h1 : term34) : term109 x.
Proof. exact (fun h0 : term110 x => @lem1380250 x h1). Qed.
Lemma lem1380253 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380254 (x : real) : (term109 x) = ((term32 x) = x).
Proof. exact (@lem1380253 ((term32 x) = x)). Qed.
Lemma lem1380255 (x : real) (h1 : term34) : (term32 x) = x.
Proof. exact (EQ_MP (@lem1380254 x) (@lem1380251 x h1)). Qed.
Lemma lem1380257 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1380258 (x : real) (y : real) : (real_add x y) = (real_add x y).
Proof. exact (@lem1380257 (real_add x y)). Qed.
Lemma lem1380259 (x : real) (y : real) : term111 x y.
Proof. exact (fun h0 : term112 x y => @lem1380258 x y). Qed.
Lemma lem1380261 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380262 (x : real) (y : real) : (term111 x y) = ((real_add x y) = (real_add x y)).
Proof. exact (@lem1380261 ((real_add x y) = (real_add x y))). Qed.
Lemma lem1380263 (x : real) (y : real) : (real_add x y) = (real_add x y).
Proof. exact (EQ_MP (@lem1380262 x y) (@lem1380259 x y)). Qed.
Lemma lem1380265 (x : real) (y : real) (h1 : term47 x y) : term113 y.
Proof. exact (proj2 (@lem1380055 x y h1)). Qed.
Lemma lem1380266 (x : real) (y : real) (h1 : term47 x y) : term114 y.
Proof. exact (fun h0 : term115 y => @lem1380265 x y h1). Qed.
Lemma lem1380268 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380269 (y : real) : (term114 y) = (term113 y).
Proof. exact (@lem1380268 (term113 y)). Qed.
Lemma lem1380270 (x : real) (y : real) (h1 : term47 x y) : term113 y.
Proof. exact (EQ_MP (@lem1380269 y) (@lem1380266 x y h1)). Qed.
Lemma lem1380276 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1380277 (_24452 : real) (_24453 : real) (_24454 : real) : (term78 _24453 _24452 _24454) = (term116 _24452 _24453 _24454).
Proof. exact (@lem1380276 (term79 _24453 _24452 _24454) (term95 _24453 _24454)). Qed.
Lemma lem1380283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1380284 (_24452 : real) (_24453 : real) (_24454 : real) : (term117 _24453 _24452 _24454) = (term118 _24452 _24453 _24454).
Proof. exact (MK_COMB (@lem1380283) (@lem1380277 _24452 _24453 _24454)). Qed.
Lemma lem1380290 (_24452 : real) (_24453 : real) (_24454 : real) : (term116 _24452 _24453 _24454) = (term116 _24452 _24453 _24454).
Proof. exact (eq_refl (term116 _24452 _24453 _24454)). Qed.
Lemma lem1380291 (_24452 : real) (_24453 : real) (_24454 : real) : ((term78 _24453 _24452 _24454) = (term116 _24452 _24453 _24454)) = ((term116 _24452 _24453 _24454) = (term116 _24452 _24453 _24454)).
Proof. exact (MK_COMB (@lem1380284 _24452 _24453 _24454) (@lem1380290 _24452 _24453 _24454)). Qed.
Lemma lem1380293 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1380294 (x : Prop) : (x = x) = True.
Proof. exact (@lem1380293 Prop x). Qed.
Lemma lem1380295 (_24452 : real) (_24453 : real) (_24454 : real) : ((term116 _24452 _24453 _24454) = (term116 _24452 _24453 _24454)) = True.
Proof. exact (@lem1380294 (term116 _24452 _24453 _24454)). Qed.
Lemma lem1380296 (_24452 : real) (_24453 : real) (_24454 : real) : ((term78 _24453 _24452 _24454) = (term116 _24452 _24453 _24454)) = True.
Proof. exact (TRANS (@lem1380291 _24452 _24453 _24454) (@lem1380295 _24452 _24453 _24454)). Qed.
Lemma lem1380297 (_24452 : real) (_24453 : real) (_24454 : real) : True = ((term78 _24453 _24452 _24454) = (term116 _24452 _24453 _24454)).
Proof. exact (SYM (@lem1380296 _24452 _24453 _24454)). Qed.
Lemma lem1380298 (_24452 : real) (_24453 : real) (_24454 : real) : (term78 _24453 _24452 _24454) = (term116 _24452 _24453 _24454).
Proof. exact (EQ_MP (@lem1380297 _24452 _24453 _24454) (@lem0)). Qed.
Lemma lem1380299 (_24452 : real) (_24453 : real) (_24454 : real) (h1 : term17) : term116 _24452 _24453 _24454.
Proof. exact (EQ_MP (@lem1380298 _24452 _24453 _24454) (@lem1380161 _24453 _24452 _24454 h1)). Qed.
Lemma lem1380301 (b : Prop) (a : Prop) : (a \/ b) = (term119 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1380302 (_24453 : real) (_24452 : real) (_24454 : real) : (term116 _24452 _24453 _24454) = (term120 _24453 _24452 _24454).
Proof. exact (@lem1380301 (term95 _24453 _24454) (term79 _24453 _24452 _24454)). Qed.
Lemma lem1380304 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1380305 (_24453 : real) (_24454 : real) : (term122 _24453 _24454) = (real_le _24453 _24454).
Proof. exact (@lem1380304 (real_le _24453 _24454)). Qed.
Lemma lem1380306 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1380307 (_24453 : real) (_24454 : real) : (term123 _24453 _24454) = (term124 _24453 _24454).
Proof. exact (MK_COMB (@lem1380306) (@lem1380305 _24453 _24454)). Qed.
Lemma lem1380308 (_24453 : real) (_24452 : real) (_24454 : real) : (term79 _24453 _24452 _24454) = (term79 _24453 _24452 _24454).
Proof. exact (eq_refl (term79 _24453 _24452 _24454)). Qed.
Lemma lem1380309 (_24453 : real) (_24452 : real) (_24454 : real) : (term120 _24453 _24452 _24454) = (term26 _24453 _24452 _24454).
Proof. exact (MK_COMB (@lem1380307 _24453 _24454) (@lem1380308 _24453 _24452 _24454)). Qed.
Lemma lem1380310 (_24453 : real) (_24452 : real) (_24454 : real) : (term116 _24452 _24453 _24454) = (term26 _24453 _24452 _24454).
Proof. exact (TRANS (@lem1380302 _24453 _24452 _24454) (@lem1380309 _24453 _24452 _24454)). Qed.
Lemma lem1380313 (_24453 : real) (_24452 : real) (_24454 : real) (h1 : term17) : term26 _24453 _24452 _24454.
Proof. exact (EQ_MP (@lem1380310 _24453 _24452 _24454) (@lem1380299 _24452 _24453 _24454 h1)). Qed.
Lemma lem1380314 (_24452 : real) (y : real) (h1 : term17) : term125 _24452 y.
Proof. exact (@lem1380313 term126 _24452 y h1). Qed.
Lemma lem1380317 (_24452 : real) (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term127 _24452 y.
Proof. exact (@lem1380314 _24452 y h1 (@lem1380270 x y h2)). Qed.
Lemma lem1380318 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term127 x y.
Proof. exact (@lem1380317 x x y h1 h2). Qed.
Lemma lem1380319 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term128 x y.
Proof. exact (fun h0 : term129 x y => @lem1380318 x y h1 h2). Qed.
Lemma lem1380321 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380322 (x : real) (y : real) : (term128 x y) = (term127 x y).
Proof. exact (@lem1380321 (term127 x y)). Qed.
Lemma lem1380323 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term127 x y.
Proof. exact (EQ_MP (@lem1380322 x y) (@lem1380319 x y h1 h2)). Qed.
Lemma lem1380341 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1380342 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term102 _24457 _24458 _24455 _24456) = (term130 _24457 _24458 _24455 _24456).
Proof. exact (@lem1380341 (real_le _24457 _24458) (term131 _24456 _24458) (term95 _24455 _24456)). Qed.
Lemma lem1380360 (_24455 : real) (_24457 : real) : (term132 _24455 _24457) = (term132 _24455 _24457).
Proof. exact (eq_refl (term132 _24455 _24457)). Qed.
Lemma lem1380361 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term104 _24457 _24458 _24455 _24456) = (term133 _24457 _24458 _24455 _24456).
Proof. exact (MK_COMB (@lem1380360 _24455 _24457) (@lem1380342 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380365 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1380366 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term133 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456).
Proof. exact (@lem1380365 (real_le _24457 _24458) (term131 _24455 _24457) (term135 _24458 _24455 _24456)). Qed.
Lemma lem1380396 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term104 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456).
Proof. exact (TRANS (@lem1380361 _24457 _24458 _24455 _24456) (@lem1380366 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1380398 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term136 _24457 _24458 _24455 _24456) = (term137 _24457 _24458 _24455 _24456).
Proof. exact (MK_COMB (@lem1380397) (@lem1380396 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380428 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term134 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456).
Proof. exact (eq_refl (term134 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380429 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : ((term104 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456)) = ((term134 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456)).
Proof. exact (MK_COMB (@lem1380398 _24457 _24458 _24455 _24456) (@lem1380428 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380431 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1380432 (x : Prop) : (x = x) = True.
Proof. exact (@lem1380431 Prop x). Qed.
Lemma lem1380433 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : ((term134 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456)) = True.
Proof. exact (@lem1380432 (term134 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380434 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : ((term104 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456)) = True.
Proof. exact (TRANS (@lem1380429 _24457 _24458 _24455 _24456) (@lem1380433 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380435 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : True = ((term104 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456)).
Proof. exact (SYM (@lem1380434 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380436 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term104 _24457 _24458 _24455 _24456) = (term134 _24457 _24458 _24455 _24456).
Proof. exact (EQ_MP (@lem1380435 _24457 _24458 _24455 _24456) (@lem0)). Qed.
Lemma lem1380437 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : term134 _24457 _24458 _24455 _24456.
Proof. exact (EQ_MP (@lem1380436 _24457 _24458 _24455 _24456) (@lem1380186 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380439 (b : Prop) (a : Prop) : (a \/ b) = (term119 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1380440 (_24455 : real) (_24456 : real) (_24457 : real) (_24458 : real) : (term134 _24457 _24458 _24455 _24456) = (term138 _24455 _24456 _24457 _24458).
Proof. exact (@lem1380439 (term139 _24457 _24458 _24455 _24456) (real_le _24457 _24458)). Qed.
Lemma lem1380442 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1380443 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term142 _24457 _24458 _24455 _24456) = (term143 _24457 _24458 _24455 _24456).
Proof. exact (@lem1380442 (term131 _24455 _24457) (term135 _24458 _24455 _24456)). Qed.
Lemma lem1380445 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1380446 (_24455 : real) (_24457 : real) : (term144 _24455 _24457) = (_24455 = _24457).
Proof. exact (@lem1380445 (_24455 = _24457)). Qed.
Lemma lem1380447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1380448 (_24455 : real) (_24457 : real) : (term145 _24455 _24457) = (term146 _24455 _24457).
Proof. exact (MK_COMB (@lem1380447) (@lem1380446 _24455 _24457)). Qed.
Lemma lem1380450 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1380451 (_24458 : real) (_24455 : real) (_24456 : real) : (term147 _24458 _24455 _24456) = (term148 _24458 _24455 _24456).
Proof. exact (@lem1380450 (term131 _24456 _24458) (term95 _24455 _24456)). Qed.
Lemma lem1380453 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1380454 (_24456 : real) (_24458 : real) : (term144 _24456 _24458) = (_24456 = _24458).
Proof. exact (@lem1380453 (_24456 = _24458)). Qed.
Lemma lem1380455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1380456 (_24456 : real) (_24458 : real) : (term145 _24456 _24458) = (term146 _24456 _24458).
Proof. exact (MK_COMB (@lem1380455) (@lem1380454 _24456 _24458)). Qed.
Lemma lem1380458 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1380459 (_24455 : real) (_24456 : real) : (term122 _24455 _24456) = (real_le _24455 _24456).
Proof. exact (@lem1380458 (real_le _24455 _24456)). Qed.
Lemma lem1380460 (_24458 : real) (_24455 : real) (_24456 : real) : (term148 _24458 _24455 _24456) = (term149 _24458 _24455 _24456).
Proof. exact (MK_COMB (@lem1380456 _24456 _24458) (@lem1380459 _24455 _24456)). Qed.
Lemma lem1380461 (_24458 : real) (_24455 : real) (_24456 : real) : (term147 _24458 _24455 _24456) = (term149 _24458 _24455 _24456).
Proof. exact (TRANS (@lem1380451 _24458 _24455 _24456) (@lem1380460 _24458 _24455 _24456)). Qed.
Lemma lem1380462 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term143 _24457 _24458 _24455 _24456) = (term150 _24457 _24458 _24455 _24456).
Proof. exact (MK_COMB (@lem1380448 _24455 _24457) (@lem1380461 _24458 _24455 _24456)). Qed.
Lemma lem1380463 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term142 _24457 _24458 _24455 _24456) = (term150 _24457 _24458 _24455 _24456).
Proof. exact (TRANS (@lem1380443 _24457 _24458 _24455 _24456) (@lem1380462 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1380465 (_24457 : real) (_24458 : real) (_24455 : real) (_24456 : real) : (term151 _24457 _24458 _24455 _24456) = (term152 _24457 _24458 _24455 _24456).
Proof. exact (MK_COMB (@lem1380464) (@lem1380463 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380466 (_24457 : real) (_24458 : real) : (real_le _24457 _24458) = (real_le _24457 _24458).
Proof. exact (eq_refl (real_le _24457 _24458)). Qed.
Lemma lem1380467 (_24455 : real) (_24456 : real) (_24457 : real) (_24458 : real) : (term138 _24455 _24456 _24457 _24458) = (term153 _24455 _24456 _24457 _24458).
Proof. exact (MK_COMB (@lem1380465 _24457 _24458 _24455 _24456) (@lem1380466 _24457 _24458)). Qed.
Lemma lem1380468 (_24455 : real) (_24456 : real) (_24457 : real) (_24458 : real) : (term134 _24457 _24458 _24455 _24456) = (term153 _24455 _24456 _24457 _24458).
Proof. exact (TRANS (@lem1380440 _24455 _24456 _24457 _24458) (@lem1380467 _24455 _24456 _24457 _24458)). Qed.
Lemma lem1380470 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term154 x y.
Proof. exact (conj (@lem1380263 x y) (@lem1380323 x y h1 h2)). Qed.
Lemma lem1380471 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term155 x y.
Proof. exact (conj (@lem1380255 x h2) (@lem1380470 x y h1 h3)). Qed.
Lemma lem1380473 (_24455 : real) (_24456 : real) (_24457 : real) (_24458 : real) : term153 _24455 _24456 _24457 _24458.
Proof. exact (EQ_MP (@lem1380468 _24455 _24456 _24457 _24458) (@lem1380437 _24457 _24458 _24455 _24456)). Qed.
Lemma lem1380474 (x : real) (y : real) : term156 x y.
Proof. exact (@lem1380473 (term32 x) (real_add x y) x (real_add x y)). Qed.
Lemma lem1380477 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term157 x y.
Proof. exact (@lem1380474 x y (@lem1380471 x y h1 h2 h3)). Qed.
Lemma lem1380478 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term158 x y.
Proof. exact (fun h0 : term159 x y => @lem1380477 x y h1 h2 h3). Qed.
Lemma lem1380480 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380481 (x : real) (y : real) : (term158 x y) = (term157 x y).
Proof. exact (@lem1380480 (term157 x y)). Qed.
Lemma lem1380482 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term157 x y.
Proof. exact (EQ_MP (@lem1380481 x y) (@lem1380478 x y h1 h2 h3)). Qed.
Lemma lem1380488 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1380489 (_24449 : real) (_24448 : real) (_24450 : real) : (term93 _24449 _24448 _24450) = (term160 _24449 _24448 _24450).
Proof. exact (@lem1380488 (term95 _24449 _24450) (term94 _24448 _24449) (real_lt _24448 _24450)). Qed.
Lemma lem1380503 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1380504 (_24450 : real) (_24448 : real) (_24449 : real) : (term161 _24449 _24448 _24450) = (term162 _24450 _24448 _24449).
Proof. exact (@lem1380503 (real_lt _24448 _24450) (term94 _24448 _24449)). Qed.
Lemma lem1380510 (_24449 : real) (_24450 : real) : (term163 _24449 _24450) = (term163 _24449 _24450).
Proof. exact (eq_refl (term163 _24449 _24450)). Qed.
Lemma lem1380511 (_24450 : real) (_24448 : real) (_24449 : real) : (term160 _24449 _24448 _24450) = (term164 _24450 _24448 _24449).
Proof. exact (MK_COMB (@lem1380510 _24449 _24450) (@lem1380504 _24450 _24448 _24449)). Qed.
Lemma lem1380515 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1380516 (_24450 : real) (_24448 : real) (_24449 : real) : (term164 _24450 _24448 _24449) = (term165 _24450 _24448 _24449).
Proof. exact (@lem1380515 (real_lt _24448 _24450) (term95 _24449 _24450) (term94 _24448 _24449)). Qed.
Lemma lem1380532 (_24450 : real) (_24448 : real) (_24449 : real) : (term160 _24449 _24448 _24450) = (term165 _24450 _24448 _24449).
Proof. exact (TRANS (@lem1380511 _24450 _24448 _24449) (@lem1380516 _24450 _24448 _24449)). Qed.
Lemma lem1380533 (_24450 : real) (_24448 : real) (_24449 : real) : (term93 _24449 _24448 _24450) = (term165 _24450 _24448 _24449).
Proof. exact (TRANS (@lem1380489 _24449 _24448 _24450) (@lem1380532 _24450 _24448 _24449)). Qed.
Lemma lem1380534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1380535 (_24450 : real) (_24448 : real) (_24449 : real) : (term166 _24449 _24448 _24450) = (term167 _24450 _24448 _24449).
Proof. exact (MK_COMB (@lem1380534) (@lem1380533 _24450 _24448 _24449)). Qed.
Lemma lem1380549 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1380550 (_24450 : real) (_24448 : real) (_24449 : real) : (term66 _24448 _24449 _24450) = (term168 _24450 _24448 _24449).
Proof. exact (@lem1380549 (term95 _24449 _24450) (term94 _24448 _24449)). Qed.
Lemma lem1380556 (_24448 : real) (_24450 : real) : (term169 _24448 _24450) = (term169 _24448 _24450).
Proof. exact (eq_refl (term169 _24448 _24450)). Qed.
Lemma lem1380557 (_24450 : real) (_24448 : real) (_24449 : real) : (term170 _24448 _24449 _24450) = (term165 _24450 _24448 _24449).
Proof. exact (MK_COMB (@lem1380556 _24448 _24450) (@lem1380550 _24450 _24448 _24449)). Qed.
Lemma lem1380568 (_24450 : real) (_24448 : real) (_24449 : real) : ((term93 _24449 _24448 _24450) = (term170 _24448 _24449 _24450)) = ((term165 _24450 _24448 _24449) = (term165 _24450 _24448 _24449)).
Proof. exact (MK_COMB (@lem1380535 _24450 _24448 _24449) (@lem1380557 _24450 _24448 _24449)). Qed.
Lemma lem1380570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1380571 (x : Prop) : (x = x) = True.
Proof. exact (@lem1380570 Prop x). Qed.
Lemma lem1380572 (_24450 : real) (_24448 : real) (_24449 : real) : ((term165 _24450 _24448 _24449) = (term165 _24450 _24448 _24449)) = True.
Proof. exact (@lem1380571 (term165 _24450 _24448 _24449)). Qed.
Lemma lem1380573 (_24448 : real) (_24449 : real) (_24450 : real) : ((term93 _24449 _24448 _24450) = (term170 _24448 _24449 _24450)) = True.
Proof. exact (TRANS (@lem1380568 _24450 _24448 _24449) (@lem1380572 _24450 _24448 _24449)). Qed.
Lemma lem1380574 (_24448 : real) (_24449 : real) (_24450 : real) : True = ((term93 _24449 _24448 _24450) = (term170 _24448 _24449 _24450)).
Proof. exact (SYM (@lem1380573 _24448 _24449 _24450)). Qed.
Lemma lem1380575 (_24448 : real) (_24449 : real) (_24450 : real) : (term93 _24449 _24448 _24450) = (term170 _24448 _24449 _24450).
Proof. exact (EQ_MP (@lem1380574 _24448 _24449 _24450) (@lem0)). Qed.
Lemma lem1380576 (_24448 : real) (_24449 : real) (_24450 : real) (h1 : term41) : term170 _24448 _24449 _24450.
Proof. exact (EQ_MP (@lem1380575 _24448 _24449 _24450) (@lem1380153 _24449 _24448 _24450 h1)). Qed.
Lemma lem1380578 (b : Prop) (a : Prop) : (a \/ b) = (term119 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1380579 (_24449 : real) (_24448 : real) (_24450 : real) : (term170 _24448 _24449 _24450) = (term171 _24449 _24448 _24450).
Proof. exact (@lem1380578 (term66 _24448 _24449 _24450) (real_lt _24448 _24450)). Qed.
Lemma lem1380581 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1380582 (_24448 : real) (_24449 : real) (_24450 : real) : (term172 _24448 _24449 _24450) = (term173 _24448 _24449 _24450).
Proof. exact (@lem1380581 (term94 _24448 _24449) (term95 _24449 _24450)). Qed.
Lemma lem1380584 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1380585 (_24448 : real) (_24449 : real) : (term174 _24448 _24449) = (real_lt _24448 _24449).
Proof. exact (@lem1380584 (real_lt _24448 _24449)). Qed.
Lemma lem1380586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1380587 (_24448 : real) (_24449 : real) : (term175 _24448 _24449) = (term176 _24448 _24449).
Proof. exact (MK_COMB (@lem1380586) (@lem1380585 _24448 _24449)). Qed.
Lemma lem1380589 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1380590 (_24449 : real) (_24450 : real) : (term122 _24449 _24450) = (real_le _24449 _24450).
Proof. exact (@lem1380589 (real_le _24449 _24450)). Qed.
Lemma lem1380591 (_24448 : real) (_24449 : real) (_24450 : real) : (term173 _24448 _24449 _24450) = (term71 _24448 _24449 _24450).
Proof. exact (MK_COMB (@lem1380587 _24448 _24449) (@lem1380590 _24449 _24450)). Qed.
Lemma lem1380592 (_24448 : real) (_24449 : real) (_24450 : real) : (term172 _24448 _24449 _24450) = (term71 _24448 _24449 _24450).
Proof. exact (TRANS (@lem1380582 _24448 _24449 _24450) (@lem1380591 _24448 _24449 _24450)). Qed.
Lemma lem1380593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1380594 (_24448 : real) (_24449 : real) (_24450 : real) : (term177 _24448 _24449 _24450) = (term178 _24448 _24449 _24450).
Proof. exact (MK_COMB (@lem1380593) (@lem1380592 _24448 _24449 _24450)). Qed.
Lemma lem1380595 (_24448 : real) (_24450 : real) : (real_lt _24448 _24450) = (real_lt _24448 _24450).
Proof. exact (eq_refl (real_lt _24448 _24450)). Qed.
Lemma lem1380596 (_24449 : real) (_24448 : real) (_24450 : real) : (term171 _24449 _24448 _24450) = (term35 _24449 _24448 _24450).
Proof. exact (MK_COMB (@lem1380594 _24448 _24449 _24450) (@lem1380595 _24448 _24450)). Qed.
Lemma lem1380597 (_24449 : real) (_24448 : real) (_24450 : real) : (term170 _24448 _24449 _24450) = (term35 _24449 _24448 _24450).
Proof. exact (TRANS (@lem1380579 _24449 _24448 _24450) (@lem1380596 _24449 _24448 _24450)). Qed.
Lemma lem1380599 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term179 x y.
Proof. exact (conj (@lem1380247 x y h3) (@lem1380482 x y h1 h2 h3)). Qed.
Lemma lem1380601 (_24449 : real) (_24448 : real) (_24450 : real) (h1 : term41) : term35 _24449 _24448 _24450.
Proof. exact (EQ_MP (@lem1380597 _24449 _24448 _24450) (@lem1380576 _24448 _24449 _24450 h1)). Qed.
Lemma lem1380602 (x : real) (y : real) (h1 : term41) : term180 x y.
Proof. exact (@lem1380601 x term126 (real_add x y) h1). Qed.
Lemma lem1380605 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term49 x y.
Proof. exact (@lem1380602 x y h1 (@lem1380599 x y h2 h3 h4)). Qed.
Lemma lem1380606 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term181 x y.
Proof. exact (fun h0 : term96 x y => @lem1380605 x y h1 h2 h3 h4). Qed.
Lemma lem1380608 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380609 (x : real) (y : real) : (term181 x y) = (term49 x y).
Proof. exact (@lem1380608 (term49 x y)). Qed.
Lemma lem1380610 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term49 x y.
Proof. exact (EQ_MP (@lem1380609 x y) (@lem1380606 x y h1 h2 h3 h4)). Qed.
Lemma lem1380613 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1380615 (x : real) (y : real) : (term96 x y) = (term182 x y).
Proof. exact (@lem1380613 (term49 x y)). Qed.
Lemma lem1380618 (x : real) (y : real) (h1 : term47 x y) : term182 x y.
Proof. exact (EQ_MP (@lem1380615 x y) (@lem1380163 x y h1)). Qed.
Lemma lem1380621 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (@lem1380618 x y h4 (@lem1380610 x y h1 h2 h3 h4)). Qed.
Lemma lem1380622 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term183.
Proof. exact (fun h0 : ~ False => @lem1380621 x y h1 h2 h3 h4). Qed.
Lemma lem1380624 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1380625 : term183 = False.
Proof. exact (@lem1380624 False). Qed.
Lemma lem1380626 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1380625) (@lem1380622 x y h1 h2 h3 h4)). Qed.
Lemma lem1380627 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1380626 x y h1 h2 h3 h4) (fun h5 : False => @lem1380089 h3)). Qed.
Lemma lem1380628 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1380627 x y h1 h2 h3 h4) (@lem1380089 h3)). Qed.
Lemma lem1380629 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : (term47 x y) = False.
Proof. exact (prop_ext (fun h5 : term47 x y => @lem1380628 x y h1 h2 h3 h4) (fun h5 : False => @lem1380053 x y h4)). Qed.
Lemma lem1380630 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1380629 x y h1 h2 h3 h4) (@lem1380053 x y h4)). Qed.
Lemma lem1380631 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1380630 x y h1 h2 h3 h4) (fun h5 : False => @lem1379980 h3)). Qed.
Lemma lem1380632 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1380631 x y h1 h2 h3 h4) (@lem1379980 h3)). Qed.
Lemma lem1380633 (x : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term58 x) : False.
Proof. exact (ex_elim (@lem1379927 x h4) (fun y : real => fun h0 : term57 x y => @lem1380632 x y h1 h2 h3 h0)). Qed.
Lemma lem1380634 (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1379753 h4) (fun x : real => fun h0 : term63 x => @lem1380633 x h1 h2 h3 h0)). Qed.
Lemma lem1380635 (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term10) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1380634 h1 h2 h3 h4) (fun h5 : False => @lem1379849 h3)). Qed.
Lemma lem1380636 (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term10) : False.
Proof. exact (EQ_MP (@lem1380635 h1 h2 h3 h4) (@lem1379849 h3)). Qed.
Lemma lem1380637 (h1 : term41) (h2 : term34) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1380636 h1 h0 h2 h3). Qed.
Lemma lem1380638 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1380639 (h1 : term41) (h2 : term34) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1380638) (@lem1380637 h1 h2 h3)). Qed.
Lemma lem1380640 (h1 : term41) (h2 : term10) : term20.
Proof. exact (fun h0 : term34 => @lem1380639 h1 h0 h2). Qed.
Lemma lem1380641 (h1 : term10) : term23.
Proof. exact (fun h0 : term41 => @lem1380640 h0 h1). Qed.
Lemma lem1380642 : term25.
Proof. exact (fun h0 : term10 => @lem1380641 h0). Qed.
Lemma lem1380643 : term11.
Proof. exact (EQ_MP (@lem1379661) (@lem1380642)). Qed.
Lemma lem1380645 : term11.
Proof. exact (@lem1379452 (@lem1380643)). Qed.
Lemma lem1380646 (h1 : term10) : term22.
Proof. exact (@lem1380645 (@lem1379437 h1)). Qed.
Lemma lem1380647 (h1 : term10) : term19.
Proof. exact (@lem1380646 h1 (@lem1370312)). Qed.
Lemma lem1380648 (h1 : term10) : term15.
Proof. exact (@lem1380647 h1 (@lem1361590)). Qed.
Lemma lem1380649 (h1 : term10) : False.
Proof. exact (@lem1380648 h1 (@lem1339889)). Qed.
Lemma lem1380650 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1380649 h1) (fun h2 : False => @lem1379437 h1)). Qed.
Lemma lem1380651 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1380650 h1) (@lem1379437 h1)). Qed.
Lemma lem1380652 : term9.
Proof. exact (fun h0 : term10 => @lem1380651 h0). Qed.
Lemma lem1380653 : term8.
Proof. exact (EQ_MP (@lem1379436) (@lem1380652)). Qed.
