Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUNDS_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_ADD_RDISTRIB_spec.
Require Import REAL_CONVEX_BOUND2_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338986_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1685654 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1685655 (u : real) (v : real) (a : real) : (term1 u v a) = (term2 u v a).
Proof. exact (@lem1685654 (term1 u v a)). Qed.
Lemma lem1685656 (u : real) (v : real) (a : real) : (term2 u v a) = (term1 u v a).
Proof. exact (SYM (@lem1685655 u v a)). Qed.
Lemma lem1685657 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1685660 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1685661 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1685660 u v a h0). Qed.
Lemma lem1685662 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1685663 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1685664 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1685662 u v a h2 (@lem1685663 u v a h1)). Qed.
Lemma lem1685665 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term6 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1685664 u v a h1 h0). Qed.
Lemma lem1685666 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1685667 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1685665 u v a h1 (@lem1685666 u v a h2)). Qed.
Lemma lem1685668 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1685667 u v a h0 h1). Qed.
Lemma lem1685669 (u : real) (v : real) (a : real) : term7 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1685668 u v a h0). Qed.
Lemma lem1685672 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (@lem1685669 u v a (@lem1685661 u v a)). Qed.
Lemma lem1685704 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1685705 : term8 = term9.
Proof. exact (@lem1685704 term10). Qed.
Lemma lem1685710 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1685711 : term12 = term13.
Proof. exact (MK_COMB (@lem1685710) (@lem1685705)). Qed.
Lemma lem1685714 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1685715 (u : real) (v : real) (a : real) : (term4 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1685714 u v a) (@lem1685711)). Qed.
Lemma lem1685718 (v : real) (a : real) : (term16 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1685715 u v a)). Qed.
Lemma lem1685719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685720 (v : real) (a : real) : (term18 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1685719) (@lem1685718 v a)). Qed.
Lemma lem1685725 (a : real) : (term20 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1685720 v a)). Qed.
Lemma lem1685726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685727 (a : real) : (term22 a) = (term23 a).
Proof. exact (MK_COMB (@lem1685726) (@lem1685725 a)). Qed.
Lemma lem1685732 : term24 = term25.
Proof. exact (fun_ext (fun a : real => @lem1685727 a)). Qed.
Lemma lem1685733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685742 : term26 = term27.
Proof. exact (MK_COMB (@lem1685733) (@lem1685732)). Qed.
Lemma lem1685743 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1685744 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1685743 x)). Qed.
Lemma lem1685745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685746 : term10 = term10.
Proof. exact (MK_COMB (@lem1685745) (@lem1685744)). Qed.
Lemma lem1685747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1685748 : term9 = term9.
Proof. exact (MK_COMB (@lem1685747) (@lem1685746)). Qed.
Lemma lem1685749 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1685750 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1685749 x y z)). Qed.
Lemma lem1685751 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685752 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1685751) (@lem1685750 x y)). Qed.
Lemma lem1685753 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1685752 x y)). Qed.
Lemma lem1685754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685755 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1685754) (@lem1685753 x)). Qed.
Lemma lem1685756 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1685755 x)). Qed.
Lemma lem1685757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685758 : term37 = term37.
Proof. exact (MK_COMB (@lem1685757) (@lem1685756)). Qed.
Lemma lem1685759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1685760 : term11 = term11.
Proof. exact (MK_COMB (@lem1685759) (@lem1685758)). Qed.
Lemma lem1685761 : term13 = term13.
Proof. exact (MK_COMB (@lem1685760) (@lem1685748)). Qed.
Lemma lem1685770 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1685771 (u : real) (v : real) (a : real) : (term15 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1685770 u v a) (@lem1685761)). Qed.
Lemma lem1685772 (v : real) (a : real) : (term17 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1685771 u v a)). Qed.
Lemma lem1685773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685774 (v : real) (a : real) : (term19 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1685773) (@lem1685772 v a)). Qed.
Lemma lem1685775 (a : real) : (term21 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1685774 v a)). Qed.
Lemma lem1685776 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685777 (a : real) : (term23 a) = (term23 a).
Proof. exact (MK_COMB (@lem1685776) (@lem1685775 a)). Qed.
Lemma lem1685778 : term25 = term25.
Proof. exact (fun_ext (fun a : real => @lem1685777 a)). Qed.
Lemma lem1685779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685780 : term27 = term27.
Proof. exact (MK_COMB (@lem1685779) (@lem1685778)). Qed.
Lemma lem1685831 : term26 = term27.
Proof. exact (TRANS (@lem1685742) (@lem1685780)). Qed.
Lemma lem1685832 : term27 = term26.
Proof. exact (SYM (@lem1685831)). Qed.
Lemma lem1685833 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1685834 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1685835 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1685846 (u : real) (v : real) (a : real) : (term3 u v a) = (term38 u v a).
Proof. exact (@lem17362 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1685848 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1685849 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1685848 x y z)). Qed.
Lemma lem1685850 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685851 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1685850) (@lem1685849 x y)). Qed.
Lemma lem1685852 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1685851 x y)). Qed.
Lemma lem1685853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685854 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1685853) (@lem1685852 x)). Qed.
Lemma lem1685855 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1685854 x)). Qed.
Lemma lem1685856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685873 : term37 = term37.
Proof. exact (MK_COMB (@lem1685856) (@lem1685855)). Qed.
Lemma lem1685874 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1685873) (@lem1685834 h1)). Qed.
Lemma lem1685875 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1685876 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1685875 x)). Qed.
Lemma lem1685877 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685886 : term10 = term10.
Proof. exact (MK_COMB (@lem1685877) (@lem1685876)). Qed.
Lemma lem1685887 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1685886) (@lem1685835 h1)). Qed.
Lemma lem1685925 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term38 u v a.
Proof. exact (EQ_MP (@lem1685846 u v a) (@lem1685833 u v a h1)). Qed.
Lemma lem1685950 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1685951 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1685950 x y z)). Qed.
Lemma lem1685952 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685953 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1685952) (@lem1685951 x y)). Qed.
Lemma lem1685954 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1685953 x y)). Qed.
Lemma lem1685955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685956 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1685955) (@lem1685954 x)). Qed.
Lemma lem1685957 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1685956 x)). Qed.
Lemma lem1685958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685959 : term37 = term37.
Proof. exact (MK_COMB (@lem1685958) (@lem1685957)). Qed.
Lemma lem1685960 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1685959) (@lem1685874 h1)). Qed.
Lemma lem1685975 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1685976 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1685975 x)). Qed.
Lemma lem1685977 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685978 : term10 = term10.
Proof. exact (MK_COMB (@lem1685977) (@lem1685976)). Qed.
Lemma lem1685979 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1685978) (@lem1685887 h1)). Qed.
Lemma lem1685983 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1685984 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1685983 x y z)). Qed.
Lemma lem1685985 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685986 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1685985) (@lem1685984 x y)). Qed.
Lemma lem1685987 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1685986 x y)). Qed.
Lemma lem1685988 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685989 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1685988) (@lem1685987 x)). Qed.
Lemma lem1685990 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1685989 x)). Qed.
Lemma lem1685991 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1685993 : term37 = term37.
Proof. exact (MK_COMB (@lem1685991) (@lem1685990)). Qed.
Lemma lem1685994 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1685993) (@lem1685960 h1)). Qed.
Lemma lem1685996 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1685997 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1685996 x)). Qed.
Lemma lem1685998 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686000 : term10 = term10.
Proof. exact (MK_COMB (@lem1685998) (@lem1685997)). Qed.
Lemma lem1686001 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1686000) (@lem1685979 h1)). Qed.
Lemma lem1686010 (_26005 : real) (h1 : term37) : term40 _26005.
Proof. exact (@lem1685994 h1 _26005). Qed.
Lemma lem1686011 (_26005 : real) : (term40 _26005) = (term35 _26005).
Proof. exact (eq_refl (term40 _26005)). Qed.
Lemma lem1686012 (_26005 : real) (h1 : term37) : term35 _26005.
Proof. exact (EQ_MP (@lem1686011 _26005) (@lem1686010 _26005 h1)). Qed.
Lemma lem1686013 (_26005 : real) (_26006 : real) (h1 : term37) : term41 _26005 _26006.
Proof. exact (@lem1686012 _26005 h1 _26006). Qed.
Lemma lem1686014 (_26005 : real) (_26006 : real) : (term41 _26005 _26006) = (term33 _26005 _26006).
Proof. exact (eq_refl (term41 _26005 _26006)). Qed.
Lemma lem1686015 (_26005 : real) (_26006 : real) (h1 : term37) : term33 _26005 _26006.
Proof. exact (EQ_MP (@lem1686014 _26005 _26006) (@lem1686013 _26005 _26006 h1)). Qed.
Lemma lem1686016 (_26005 : real) (_26006 : real) (_26007 : real) (h1 : term37) : term42 _26005 _26006 _26007.
Proof. exact (@lem1686015 _26005 _26006 h1 _26007). Qed.
Lemma lem1686017 (_26005 : real) (_26006 : real) (_26007 : real) : (term42 _26005 _26006 _26007) = ((term30 _26005 _26006 _26007) = (term31 _26005 _26006 _26007)).
Proof. exact (eq_refl (term42 _26005 _26006 _26007)). Qed.
Lemma lem1686019 (_26008 : real) (h1 : term10) : term43 _26008.
Proof. exact (@lem1686001 h1 _26008). Qed.
Lemma lem1686020 (_26008 : real) : (term43 _26008) = ((term28 _26008) = _26008).
Proof. exact (eq_refl (term43 _26008)). Qed.
Lemma lem1686029 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term44 u v a.
Proof. exact (proj2 (@lem1685925 u v a h1)). Qed.
Lemma lem1686054 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1686055 (_26015 : real) (_26017 : real) (h1 : _26015 = _26017) : _26015 = _26017.
Proof. exact (h1). Qed.
Lemma lem1686056 (_26016 : real) (_26018 : real) (h1 : _26016 = _26018) : _26016 = _26018.
Proof. exact (h1). Qed.
Lemma lem1686057 (_26015 : real) (_26017 : real) (h1 : _26015 = _26017) : (real_mul _26015) = (real_mul _26017).
Proof. exact (MK_COMB (@lem1686054) (@lem1686055 _26015 _26017 h1)). Qed.
Lemma lem1686058 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) (h1 : _26015 = _26017) (h2 : _26016 = _26018) : (real_mul _26015 _26016) = (real_mul _26017 _26018).
Proof. exact (MK_COMB (@lem1686057 _26015 _26017 h1) (@lem1686056 _26016 _26018 h2)). Qed.
Lemma lem1686059 (_26016 : real) (_26018 : real) (_26015 : real) (_26017 : real) (h1 : _26015 = _26017) : term45 _26015 _26016 _26017 _26018.
Proof. exact (fun h0 : _26016 = _26018 => @lem1686058 _26015 _26017 _26016 _26018 h1 h0). Qed.
Lemma lem1686061 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1686062 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : (term45 _26015 _26016 _26017 _26018) = (term47 _26015 _26016 _26017 _26018).
Proof. exact (@lem1686061 (_26016 = _26018) ((real_mul _26015 _26016) = (real_mul _26017 _26018))). Qed.
Lemma lem1686063 (_26016 : real) (_26018 : real) (_26015 : real) (_26017 : real) (h1 : _26015 = _26017) : term47 _26015 _26016 _26017 _26018.
Proof. exact (EQ_MP (@lem1686062 _26015 _26016 _26017 _26018) (@lem1686059 _26016 _26018 _26015 _26017 h1)). Qed.
Lemma lem1686064 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : term48 _26015 _26016 _26017 _26018.
Proof. exact (fun h0 : _26015 = _26017 => @lem1686063 _26016 _26018 _26015 _26017 h0). Qed.
Lemma lem1686066 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1686067 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : (term48 _26015 _26016 _26017 _26018) = (term49 _26015 _26016 _26017 _26018).
Proof. exact (@lem1686066 (_26015 = _26017) (term47 _26015 _26016 _26017 _26018)). Qed.
Lemma lem1686068 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : term49 _26015 _26016 _26017 _26018.
Proof. exact (EQ_MP (@lem1686067 _26015 _26016 _26017 _26018) (@lem1686064 _26015 _26016 _26017 _26018)). Qed.
Lemma lem1686085 (x : real) (y : real) (z : real) : term50 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1686089 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (proj1 (@lem1685925 u v a h1)). Qed.
Lemma lem1686090 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1686089 u v a h1). Qed.
Lemma lem1686092 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686093 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1686092 ((real_add u v) = term39)). Qed.
Lemma lem1686094 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1686093 u v) (@lem1686090 u v a h1)). Qed.
Lemma lem1686096 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1686097 (a : real) : a = a.
Proof. exact (@lem1686096 a). Qed.
Lemma lem1686098 (a : real) : term54 a.
Proof. exact (fun h0 : term55 a => @lem1686097 a). Qed.
Lemma lem1686100 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686101 (a : real) : (term54 a) = (a = a).
Proof. exact (@lem1686100 (a = a)). Qed.
Lemma lem1686102 (a : real) : a = a.
Proof. exact (EQ_MP (@lem1686101 a) (@lem1686098 a)). Qed.
Lemma lem1686120 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1686121 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term47 _26015 _26016 _26017 _26018) = (term56 _26015 _26017 _26016 _26018).
Proof. exact (@lem1686120 ((real_mul _26015 _26016) = (real_mul _26017 _26018)) (term57 _26016 _26018)). Qed.
Lemma lem1686131 (_26015 : real) (_26017 : real) : (term58 _26015 _26017) = (term58 _26015 _26017).
Proof. exact (eq_refl (term58 _26015 _26017)). Qed.
Lemma lem1686132 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term49 _26015 _26016 _26017 _26018) = (term59 _26015 _26017 _26016 _26018).
Proof. exact (MK_COMB (@lem1686131 _26015 _26017) (@lem1686121 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686136 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1686137 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term59 _26015 _26017 _26016 _26018) = (term61 _26015 _26017 _26016 _26018).
Proof. exact (@lem1686136 ((real_mul _26015 _26016) = (real_mul _26017 _26018)) (term57 _26015 _26017) (term57 _26016 _26018)). Qed.
Lemma lem1686159 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term49 _26015 _26016 _26017 _26018) = (term61 _26015 _26017 _26016 _26018).
Proof. exact (TRANS (@lem1686132 _26015 _26017 _26016 _26018) (@lem1686137 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1686161 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term62 _26015 _26016 _26017 _26018) = (term63 _26015 _26017 _26016 _26018).
Proof. exact (MK_COMB (@lem1686160) (@lem1686159 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686183 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term61 _26015 _26017 _26016 _26018) = (term61 _26015 _26017 _26016 _26018).
Proof. exact (eq_refl (term61 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686184 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : ((term49 _26015 _26016 _26017 _26018) = (term61 _26015 _26017 _26016 _26018)) = ((term61 _26015 _26017 _26016 _26018) = (term61 _26015 _26017 _26016 _26018)).
Proof. exact (MK_COMB (@lem1686161 _26015 _26017 _26016 _26018) (@lem1686183 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686186 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1686187 (x : Prop) : (x = x) = True.
Proof. exact (@lem1686186 Prop x). Qed.
Lemma lem1686188 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : ((term61 _26015 _26017 _26016 _26018) = (term61 _26015 _26017 _26016 _26018)) = True.
Proof. exact (@lem1686187 (term61 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686189 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : ((term49 _26015 _26016 _26017 _26018) = (term61 _26015 _26017 _26016 _26018)) = True.
Proof. exact (TRANS (@lem1686184 _26015 _26017 _26016 _26018) (@lem1686188 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686190 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : True = ((term49 _26015 _26016 _26017 _26018) = (term61 _26015 _26017 _26016 _26018)).
Proof. exact (SYM (@lem1686189 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686191 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term49 _26015 _26016 _26017 _26018) = (term61 _26015 _26017 _26016 _26018).
Proof. exact (EQ_MP (@lem1686190 _26015 _26017 _26016 _26018) (@lem0)). Qed.
Lemma lem1686192 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : term61 _26015 _26017 _26016 _26018.
Proof. exact (EQ_MP (@lem1686191 _26015 _26017 _26016 _26018) (@lem1686068 _26015 _26016 _26017 _26018)). Qed.
Lemma lem1686194 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1686195 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : (term61 _26015 _26017 _26016 _26018) = (term65 _26015 _26016 _26017 _26018).
Proof. exact (@lem1686194 (term66 _26015 _26017 _26016 _26018) ((real_mul _26015 _26016) = (real_mul _26017 _26018))). Qed.
Lemma lem1686197 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1686198 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term69 _26015 _26017 _26016 _26018) = (term70 _26015 _26017 _26016 _26018).
Proof. exact (@lem1686197 (term57 _26015 _26017) (term57 _26016 _26018)). Qed.
Lemma lem1686200 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1686201 (_26015 : real) (_26017 : real) : (term72 _26015 _26017) = (_26015 = _26017).
Proof. exact (@lem1686200 (_26015 = _26017)). Qed.
Lemma lem1686202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1686203 (_26015 : real) (_26017 : real) : (term73 _26015 _26017) = (term74 _26015 _26017).
Proof. exact (MK_COMB (@lem1686202) (@lem1686201 _26015 _26017)). Qed.
Lemma lem1686205 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1686206 (_26016 : real) (_26018 : real) : (term72 _26016 _26018) = (_26016 = _26018).
Proof. exact (@lem1686205 (_26016 = _26018)). Qed.
Lemma lem1686207 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term70 _26015 _26017 _26016 _26018) = (term75 _26015 _26017 _26016 _26018).
Proof. exact (MK_COMB (@lem1686203 _26015 _26017) (@lem1686206 _26016 _26018)). Qed.
Lemma lem1686208 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term69 _26015 _26017 _26016 _26018) = (term75 _26015 _26017 _26016 _26018).
Proof. exact (TRANS (@lem1686198 _26015 _26017 _26016 _26018) (@lem1686207 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686209 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1686210 (_26015 : real) (_26017 : real) (_26016 : real) (_26018 : real) : (term76 _26015 _26017 _26016 _26018) = (term77 _26015 _26017 _26016 _26018).
Proof. exact (MK_COMB (@lem1686209) (@lem1686208 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686211 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : ((real_mul _26015 _26016) = (real_mul _26017 _26018)) = ((real_mul _26015 _26016) = (real_mul _26017 _26018)).
Proof. exact (eq_refl ((real_mul _26015 _26016) = (real_mul _26017 _26018))). Qed.
Lemma lem1686212 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : (term65 _26015 _26016 _26017 _26018) = (term78 _26015 _26016 _26017 _26018).
Proof. exact (MK_COMB (@lem1686210 _26015 _26017 _26016 _26018) (@lem1686211 _26015 _26016 _26017 _26018)). Qed.
Lemma lem1686213 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : (term61 _26015 _26017 _26016 _26018) = (term78 _26015 _26016 _26017 _26018).
Proof. exact (TRANS (@lem1686195 _26015 _26016 _26017 _26018) (@lem1686212 _26015 _26016 _26017 _26018)). Qed.
Lemma lem1686215 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term79 u v a.
Proof. exact (conj (@lem1686094 u v a h1) (@lem1686102 a)). Qed.
Lemma lem1686217 (_26015 : real) (_26016 : real) (_26017 : real) (_26018 : real) : term78 _26015 _26016 _26017 _26018.
Proof. exact (EQ_MP (@lem1686213 _26015 _26016 _26017 _26018) (@lem1686192 _26015 _26017 _26016 _26018)). Qed.
Lemma lem1686218 (u : real) (v : real) (a : real) : term80 u v a.
Proof. exact (@lem1686217 (real_add u v) a term39 a). Qed.
Lemma lem1686221 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (@lem1686218 u v a (@lem1686215 u v a h1)). Qed.
Lemma lem1686222 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term81 u v a.
Proof. exact (fun h0 : term82 u v a => @lem1686221 u v a h1). Qed.
Lemma lem1686224 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686225 (u : real) (v : real) (a : real) : (term81 u v a) = ((term30 u v a) = (term28 a)).
Proof. exact (@lem1686224 ((term30 u v a) = (term28 a))). Qed.
Lemma lem1686226 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (EQ_MP (@lem1686225 u v a) (@lem1686222 u v a h1)). Qed.
Lemma lem1686228 (_26005 : real) (_26006 : real) (_26007 : real) (h1 : term37) : (term30 _26005 _26006 _26007) = (term31 _26005 _26006 _26007).
Proof. exact (EQ_MP (@lem1686017 _26005 _26006 _26007) (@lem1686016 _26005 _26006 _26007 h1)). Qed.
Lemma lem1686229 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (@lem1686228 u v a h1). Qed.
Lemma lem1686230 (u : real) (v : real) (a : real) (h1 : term37) : term83 u v a.
Proof. exact (fun h0 : term84 u v a => @lem1686229 u v a h1). Qed.
Lemma lem1686232 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686233 (u : real) (v : real) (a : real) : (term83 u v a) = ((term30 u v a) = (term31 u v a)).
Proof. exact (@lem1686232 ((term30 u v a) = (term31 u v a))). Qed.
Lemma lem1686234 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1686233 u v a) (@lem1686230 u v a h1)). Qed.
Lemma lem1686252 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1686253 (y : real) (x : real) (z : real) : (term85 x y z) = (term86 y x z).
Proof. exact (@lem1686252 (y = z) (term57 x z)). Qed.
Lemma lem1686263 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1686264 (y : real) (x : real) (z : real) : (term50 x y z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1686263 x y) (@lem1686253 y x z)). Qed.
Lemma lem1686268 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1686269 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1686268 (y = z) (term57 x y) (term57 x z)). Qed.
Lemma lem1686291 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (TRANS (@lem1686264 y x z) (@lem1686269 y x z)). Qed.
Lemma lem1686292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1686293 (y : real) (x : real) (z : real) : (term89 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1686292) (@lem1686291 y x z)). Qed.
Lemma lem1686315 (y : real) (x : real) (z : real) : (term88 y x z) = (term88 y x z).
Proof. exact (eq_refl (term88 y x z)). Qed.
Lemma lem1686316 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = ((term88 y x z) = (term88 y x z)).
Proof. exact (MK_COMB (@lem1686293 y x z) (@lem1686315 y x z)). Qed.
Lemma lem1686318 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1686319 (x : Prop) : (x = x) = True.
Proof. exact (@lem1686318 Prop x). Qed.
Lemma lem1686320 (y : real) (x : real) (z : real) : ((term88 y x z) = (term88 y x z)) = True.
Proof. exact (@lem1686319 (term88 y x z)). Qed.
Lemma lem1686321 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = True.
Proof. exact (TRANS (@lem1686316 y x z) (@lem1686320 y x z)). Qed.
Lemma lem1686322 (y : real) (x : real) (z : real) : True = ((term50 x y z) = (term88 y x z)).
Proof. exact (SYM (@lem1686321 y x z)). Qed.
Lemma lem1686323 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (EQ_MP (@lem1686322 y x z) (@lem0)). Qed.
Lemma lem1686324 (y : real) (x : real) (z : real) : term88 y x z.
Proof. exact (EQ_MP (@lem1686323 y x z) (@lem1686085 x y z)). Qed.
Lemma lem1686326 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1686327 (x : real) (y : real) (z : real) : (term88 y x z) = (term91 x y z).
Proof. exact (@lem1686326 (term92 y x z) (y = z)). Qed.
Lemma lem1686329 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1686330 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1686329 (term57 x y) (term57 x z)). Qed.
Lemma lem1686332 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1686333 (x : real) (y : real) : (term72 x y) = (x = y).
Proof. exact (@lem1686332 (x = y)). Qed.
Lemma lem1686334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1686335 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1686334) (@lem1686333 x y)). Qed.
Lemma lem1686337 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1686338 (x : real) (z : real) : (term72 x z) = (x = z).
Proof. exact (@lem1686337 (x = z)). Qed.
Lemma lem1686339 (y : real) (x : real) (z : real) : (term94 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1686335 x y) (@lem1686338 x z)). Qed.
Lemma lem1686340 (y : real) (x : real) (z : real) : (term93 y x z) = (term95 y x z).
Proof. exact (TRANS (@lem1686330 y x z) (@lem1686339 y x z)). Qed.
Lemma lem1686341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1686342 (y : real) (x : real) (z : real) : (term96 y x z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1686341) (@lem1686340 y x z)). Qed.
Lemma lem1686343 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1686344 (x : real) (y : real) (z : real) : (term91 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1686342 y x z) (@lem1686343 y z)). Qed.
Lemma lem1686345 (x : real) (y : real) (z : real) : (term88 y x z) = (term98 x y z).
Proof. exact (TRANS (@lem1686327 x y z) (@lem1686344 x y z)). Qed.
Lemma lem1686347 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term99 u v a.
Proof. exact (conj (@lem1686226 u v a h2) (@lem1686234 u v a h1)). Qed.
Lemma lem1686349 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1686345 x y z) (@lem1686324 y x z)). Qed.
Lemma lem1686350 (u : real) (v : real) (a : real) : term100 u v a.
Proof. exact (@lem1686349 (term30 u v a) (term28 a) (term31 u v a)). Qed.
Lemma lem1686353 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (@lem1686350 u v a (@lem1686347 u v a h1 h2)). Qed.
Lemma lem1686354 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term101 u v a.
Proof. exact (fun h0 : term102 u v a => @lem1686353 u v a h1 h2). Qed.
Lemma lem1686356 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686357 (u : real) (v : real) (a : real) : (term101 u v a) = ((term28 a) = (term31 u v a)).
Proof. exact (@lem1686356 ((term28 a) = (term31 u v a))). Qed.
Lemma lem1686358 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1686357 u v a) (@lem1686354 u v a h1 h2)). Qed.
Lemma lem1686360 (_26008 : real) (h1 : term10) : (term28 _26008) = _26008.
Proof. exact (EQ_MP (@lem1686020 _26008) (@lem1686019 _26008 h1)). Qed.
Lemma lem1686361 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (@lem1686360 a h1). Qed.
Lemma lem1686362 (a : real) (h1 : term10) : term103 a.
Proof. exact (fun h0 : term104 a => @lem1686361 a h1). Qed.
Lemma lem1686364 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686365 (a : real) : (term103 a) = ((term28 a) = a).
Proof. exact (@lem1686364 ((term28 a) = a)). Qed.
Lemma lem1686366 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (EQ_MP (@lem1686365 a) (@lem1686362 a h1)). Qed.
Lemma lem1686367 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term105 u v a.
Proof. exact (conj (@lem1686358 u v a h1 h3) (@lem1686366 a h2)). Qed.
Lemma lem1686369 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1686345 x y z) (@lem1686324 y x z)). Qed.
Lemma lem1686370 (u : real) (v : real) (a : real) : term106 u v a.
Proof. exact (@lem1686369 (term28 a) (term31 u v a) a). Qed.
Lemma lem1686373 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (@lem1686370 u v a (@lem1686367 u v a h1 h2 h3)). Qed.
Lemma lem1686374 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1686373 u v a h1 h2 h3). Qed.
Lemma lem1686376 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686377 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1686376 ((term31 u v a) = a)). Qed.
Lemma lem1686378 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1686377 u v a) (@lem1686374 u v a h1 h2 h3)). Qed.
Lemma lem1686381 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1686383 (u : real) (v : real) (a : real) : (term44 u v a) = (term108 u v a).
Proof. exact (@lem1686381 ((term31 u v a) = a)). Qed.
Lemma lem1686386 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term108 u v a.
Proof. exact (EQ_MP (@lem1686383 u v a) (@lem1686029 u v a h1)). Qed.
Lemma lem1686389 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (@lem1686386 u v a h3 (@lem1686378 u v a h1 h2 h3)). Qed.
Lemma lem1686390 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term109.
Proof. exact (fun h0 : ~ False => @lem1686389 u v a h1 h2 h3). Qed.
Lemma lem1686392 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1686393 : term109 = False.
Proof. exact (@lem1686392 False). Qed.
Lemma lem1686394 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686393) (@lem1686390 u v a h1 h2 h3)). Qed.
Lemma lem1686395 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1686394 u v a h1 h2 h3) (fun h4 : False => @lem1686001 h2)). Qed.
Lemma lem1686396 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686395 u v a h1 h2 h3) (@lem1686001 h2)). Qed.
Lemma lem1686397 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1686396 u v a h1 h2 h3) (fun h4 : False => @lem1685994 h1)). Qed.
Lemma lem1686398 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686397 u v a h1 h2 h3) (@lem1685994 h1)). Qed.
Lemma lem1686399 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1686398 u v a h1 h2 h3) (fun h4 : False => @lem1685979 h2)). Qed.
Lemma lem1686400 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686399 u v a h1 h2 h3) (@lem1685979 h2)). Qed.
Lemma lem1686401 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1686400 u v a h1 h2 h3) (fun h4 : False => @lem1685960 h1)). Qed.
Lemma lem1686402 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686401 u v a h1 h2 h3) (@lem1685960 h1)). Qed.
Lemma lem1686403 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1686402 u v a h1 h2 h3) (fun h4 : False => @lem1685887 h2)). Qed.
Lemma lem1686404 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686403 u v a h1 h2 h3) (@lem1685887 h2)). Qed.
Lemma lem1686405 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1686404 u v a h1 h2 h3) (fun h4 : False => @lem1685874 h1)). Qed.
Lemma lem1686406 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686405 u v a h1 h2 h3) (@lem1685874 h1)). Qed.
Lemma lem1686407 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term8.
Proof. exact (fun h0 : term10 => @lem1686406 u v a h1 h0 h2). Qed.
Lemma lem1686408 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1686409 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term9.
Proof. exact (EQ_MP (@lem1686408) (@lem1686407 u v a h1 h2)). Qed.
Lemma lem1686410 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term13.
Proof. exact (fun h0 : term37 => @lem1686409 u v a h0 h1). Qed.
Lemma lem1686411 (u : real) (v : real) (a : real) : term15 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1686410 u v a h0). Qed.
Lemma lem1686416 (v : real) (a : real) : term19 v a.
Proof. exact (fun u : real => @lem1686411 u v a). Qed.
Lemma lem1686421 (a : real) : term23 a.
Proof. exact (fun v : real => @lem1686416 v a). Qed.
Lemma lem1686426 : term27.
Proof. exact (fun a : real => @lem1686421 a). Qed.
Lemma lem1686427 : term26.
Proof. exact (EQ_MP (@lem1685832) (@lem1686426)). Qed.
Lemma lem1686428 (a : real) : term110 a.
Proof. exact (@lem1686427 a). Qed.
Lemma lem1686429 (a : real) : (term110 a) = (term22 a).
Proof. exact (eq_refl (term110 a)). Qed.
Lemma lem1686430 (a : real) : term22 a.
Proof. exact (EQ_MP (@lem1686429 a) (@lem1686428 a)). Qed.
Lemma lem1686431 (a : real) (v : real) : term111 a v.
Proof. exact (@lem1686430 a v). Qed.
Lemma lem1686432 (v : real) (a : real) : (term111 a v) = (term18 v a).
Proof. exact (eq_refl (term111 a v)). Qed.
Lemma lem1686433 (v : real) (a : real) : term18 v a.
Proof. exact (EQ_MP (@lem1686432 v a) (@lem1686431 a v)). Qed.
Lemma lem1686434 (v : real) (a : real) (u : real) : term112 v a u.
Proof. exact (@lem1686433 v a u). Qed.
Lemma lem1686435 (u : real) (v : real) (a : real) : (term112 v a u) = (term4 u v a).
Proof. exact (eq_refl (term112 v a u)). Qed.
Lemma lem1686436 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (EQ_MP (@lem1686435 u v a) (@lem1686434 v a u)). Qed.
Lemma lem1686438 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (@lem1685672 u v a (@lem1686436 u v a)). Qed.
Lemma lem1686439 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term12.
Proof. exact (@lem1686438 u v a (@lem1685657 u v a h1)). Qed.
Lemma lem1686440 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term8.
Proof. exact (@lem1686439 u v a h1 (@lem1487144)). Qed.
Lemma lem1686441 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (@lem1686440 u v a h1 (@lem1338986)). Qed.
Lemma lem1686442 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term3 u v a) = False.
Proof. exact (prop_ext (fun h2 : term3 u v a => @lem1686441 u v a h1) (fun h2 : False => @lem1685657 u v a h1)). Qed.
Lemma lem1686443 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1686442 u v a h1) (@lem1685657 u v a h1)). Qed.
Lemma lem1686444 (u : real) (v : real) (a : real) : term2 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1686443 u v a h0). Qed.
Lemma lem1686445 (u : real) (v : real) (a : real) : term1 u v a.
Proof. exact (EQ_MP (@lem1685656 u v a) (@lem1686444 u v a)). Qed.
Lemma lem1686446 (t1 : Prop) : term113 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1686447 (t1 : Prop) : (term113 t1) = (term114 t1).
Proof. exact (eq_refl (term113 t1)). Qed.
Lemma lem1686448 (t1 : Prop) : term114 t1.
Proof. exact (EQ_MP (@lem1686447 t1) (@lem1686446 t1)). Qed.
Lemma lem1686449 (t1 : Prop) (t2 : Prop) : term115 t1 t2.
Proof. exact (@lem1686448 t1 t2). Qed.
Lemma lem1686450 (t1 : Prop) (t2 : Prop) : (term115 t1 t2) = (term116 t1 t2).
Proof. exact (eq_refl (term115 t1 t2)). Qed.
Lemma lem1686451 (t1 : Prop) (t2 : Prop) : term116 t1 t2.
Proof. exact (EQ_MP (@lem1686450 t1 t2) (@lem1686449 t1 t2)). Qed.
Lemma lem1686452 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term117 t1 t2 t3.
Proof. exact (@lem1686451 t1 t2 t3). Qed.
Lemma lem1686453 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term117 t1 t2 t3) = ((term60 t1 t2 t3) = (term118 t1 t2 t3)).
Proof. exact (eq_refl (term117 t1 t2 t3)). Qed.
Lemma lem1686454 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term60 t1 t2 t3) = (term118 t1 t2 t3).
Proof. exact (EQ_MP (@lem1686453 t1 t2 t3) (@lem1686452 t1 t2 t3)). Qed.
Lemma lem1686455 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term118 t1 t2 t3) = (term60 t1 t2 t3).
Proof. exact (SYM (@lem1686454 t1 t2 t3)). Qed.
Lemma lem1686456 : term119.
Proof. exact (fun b : real => @lem1673888 b). Qed.
Lemma lem1686457 (u : real) (v : real) : term120 u v.
Proof. exact (fun a : real => @lem1686445 u v a). Qed.
Lemma lem1686458 (u : real) : term121 u.
Proof. exact (fun v : real => @lem1686457 u v). Qed.
Lemma lem1686459 : term122.
Proof. exact (fun u : real => @lem1686458 u). Qed.
Lemma lem1686461 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1686462 : term123 = term124.
Proof. exact (@lem1686461 term123). Qed.
Lemma lem1686463 : term124 = term123.
Proof. exact (SYM (@lem1686462)). Qed.
Lemma lem1686464 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1686467 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1686468 : term127.
Proof. exact (fun h0 : term126 => @lem1686467 h0). Qed.
Lemma lem1686469 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1686470 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1686471 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1686469 h2 (@lem1686470 h1)). Qed.
Lemma lem1686472 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem1686471 h1 h0). Qed.
Lemma lem1686473 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1686474 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1686472 h1 (@lem1686473 h2)). Qed.
Lemma lem1686475 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem1686474 h0 h1). Qed.
Lemma lem1686476 : term129.
Proof. exact (fun h0 : term127 => @lem1686475 h0). Qed.
Lemma lem1686479 : term127.
Proof. exact (@lem1686476 (@lem1686468)). Qed.
Lemma lem1686539 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1686540 : term130 = term131.
Proof. exact (@lem1686539 term119). Qed.
Lemma lem1686575 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1686576 : term133 = term134.
Proof. exact (MK_COMB (@lem1686575) (@lem1686540)). Qed.
Lemma lem1686579 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem1686586 : term126 = term136.
Proof. exact (MK_COMB (@lem1686579) (@lem1686576)). Qed.
Lemma lem1686607 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term137 x y u a v b).
Proof. exact (eq_refl (term137 x y u a v b)). Qed.
Lemma lem1686608 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term138 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1686607 x y u a v b)). Qed.
Lemma lem1686609 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686610 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term139 x y u a b).
Proof. exact (MK_COMB (@lem1686609) (@lem1686608 x y u a b)). Qed.
Lemma lem1686611 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term140 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1686610 x y u a b)). Qed.
Lemma lem1686612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686613 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term141 x y a b).
Proof. exact (MK_COMB (@lem1686612) (@lem1686611 x y a b)). Qed.
Lemma lem1686614 (x : real) (y : real) (b : real) : (term142 x y b) = (term142 x y b).
Proof. exact (fun_ext (fun a : real => @lem1686613 x y a b)). Qed.
Lemma lem1686615 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686616 (x : real) (y : real) (b : real) : (term143 x y b) = (term143 x y b).
Proof. exact (MK_COMB (@lem1686615) (@lem1686614 x y b)). Qed.
Lemma lem1686617 (x : real) (b : real) : (term144 x b) = (term144 x b).
Proof. exact (fun_ext (fun y : real => @lem1686616 x y b)). Qed.
Lemma lem1686618 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686619 (x : real) (b : real) : (term145 x b) = (term145 x b).
Proof. exact (MK_COMB (@lem1686618) (@lem1686617 x b)). Qed.
Lemma lem1686620 (b : real) : (term146 b) = (term146 b).
Proof. exact (fun_ext (fun x : real => @lem1686619 x b)). Qed.
Lemma lem1686621 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686622 (b : real) : (term147 b) = (term147 b).
Proof. exact (MK_COMB (@lem1686621) (@lem1686620 b)). Qed.
Lemma lem1686623 : term148 = term148.
Proof. exact (fun_ext (fun b : real => @lem1686622 b)). Qed.
Lemma lem1686624 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686625 : term119 = term119.
Proof. exact (MK_COMB (@lem1686624) (@lem1686623)). Qed.
Lemma lem1686626 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686627 : term131 = term131.
Proof. exact (MK_COMB (@lem1686626) (@lem1686625)). Qed.
Lemma lem1686632 (u : real) (v : real) (a : real) : (term1 u v a) = (term1 u v a).
Proof. exact (eq_refl (term1 u v a)). Qed.
Lemma lem1686633 (u : real) (v : real) : (term149 u v) = (term149 u v).
Proof. exact (fun_ext (fun a : real => @lem1686632 u v a)). Qed.
Lemma lem1686634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686635 (u : real) (v : real) : (term120 u v) = (term120 u v).
Proof. exact (MK_COMB (@lem1686634) (@lem1686633 u v)). Qed.
Lemma lem1686636 (u : real) : (term150 u) = (term150 u).
Proof. exact (fun_ext (fun v : real => @lem1686635 u v)). Qed.
Lemma lem1686637 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686638 (u : real) : (term121 u) = (term121 u).
Proof. exact (MK_COMB (@lem1686637) (@lem1686636 u)). Qed.
Lemma lem1686639 : term151 = term151.
Proof. exact (fun_ext (fun u : real => @lem1686638 u)). Qed.
Lemma lem1686640 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686641 : term122 = term122.
Proof. exact (MK_COMB (@lem1686640) (@lem1686639)). Qed.
Lemma lem1686642 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1686643 : term132 = term132.
Proof. exact (MK_COMB (@lem1686642) (@lem1686641)). Qed.
Lemma lem1686644 : term134 = term134.
Proof. exact (MK_COMB (@lem1686643) (@lem1686627)). Qed.
Lemma lem1686677 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term152 a u x v y b) = (term152 a u x v y b).
Proof. exact (eq_refl (term152 a u x v y b)). Qed.
Lemma lem1686678 (a : real) (u : real) (x : real) (y : real) (b : real) : (term153 a u x y b) = (term153 a u x y b).
Proof. exact (fun_ext (fun v : real => @lem1686677 a u x v y b)). Qed.
Lemma lem1686679 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686680 (a : real) (u : real) (x : real) (y : real) (b : real) : (term154 a u x y b) = (term154 a u x y b).
Proof. exact (MK_COMB (@lem1686679) (@lem1686678 a u x y b)). Qed.
Lemma lem1686681 (a : real) (x : real) (y : real) (b : real) : (term155 a x y b) = (term155 a x y b).
Proof. exact (fun_ext (fun u : real => @lem1686680 a u x y b)). Qed.
Lemma lem1686682 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686683 (a : real) (x : real) (y : real) (b : real) : (term156 a x y b) = (term156 a x y b).
Proof. exact (MK_COMB (@lem1686682) (@lem1686681 a x y b)). Qed.
Lemma lem1686684 (a : real) (x : real) (y : real) : (term157 a x y) = (term157 a x y).
Proof. exact (fun_ext (fun b : real => @lem1686683 a x y b)). Qed.
Lemma lem1686685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686686 (a : real) (x : real) (y : real) : (term158 a x y) = (term158 a x y).
Proof. exact (MK_COMB (@lem1686685) (@lem1686684 a x y)). Qed.
Lemma lem1686687 (x : real) (y : real) : (term159 x y) = (term159 x y).
Proof. exact (fun_ext (fun a : real => @lem1686686 a x y)). Qed.
Lemma lem1686688 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686689 (x : real) (y : real) : (term160 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1686688) (@lem1686687 x y)). Qed.
Lemma lem1686690 (x : real) : (term161 x) = (term161 x).
Proof. exact (fun_ext (fun y : real => @lem1686689 x y)). Qed.
Lemma lem1686691 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686692 (x : real) : (term162 x) = (term162 x).
Proof. exact (MK_COMB (@lem1686691) (@lem1686690 x)). Qed.
Lemma lem1686693 : term163 = term163.
Proof. exact (fun_ext (fun x : real => @lem1686692 x)). Qed.
Lemma lem1686694 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1686695 : term123 = term123.
Proof. exact (MK_COMB (@lem1686694) (@lem1686693)). Qed.
Lemma lem1686696 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686697 : term125 = term125.
Proof. exact (MK_COMB (@lem1686696) (@lem1686695)). Qed.
Lemma lem1686698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1686699 : term135 = term135.
Proof. exact (MK_COMB (@lem1686698) (@lem1686697)). Qed.
Lemma lem1686700 : term136 = term136.
Proof. exact (MK_COMB (@lem1686699) (@lem1686644)). Qed.
Lemma lem1686825 : term126 = term136.
Proof. exact (TRANS (@lem1686586) (@lem1686700)). Qed.
Lemma lem1686826 : term136 = term126.
Proof. exact (SYM (@lem1686825)). Qed.
Lemma lem1686827 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1686828 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem1686829 (h1 : term119) : term119.
Proof. exact (h1). Qed.
Lemma lem1686861 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term164 a u x v y b) = (term165 a u x v y b).
Proof. exact (@lem17045 (term166 a u x v y) (term167 u x v y b)). Qed.
Lemma lem1686863 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term168 x a y b u v) = (term168 x a y b u v).
Proof. exact (eq_refl (term168 x a y b u v)). Qed.
Lemma lem1686864 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term169 a u x v y b) = (term170 a u x v y b).
Proof. exact (MK_COMB (@lem1686863 x a y b u v) (@lem1686861 a u x v y b)). Qed.
Lemma lem1686865 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term171 a u x v y b) = (term169 a u x v y b).
Proof. exact (@lem17362 (term172 x a y b u v) (term173 a u x v y b)). Qed.
Lemma lem1686866 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term171 a u x v y b) = (term170 a u x v y b).
Proof. exact (TRANS (@lem1686865 a u x v y b) (@lem1686864 a u x v y b)). Qed.
Lemma lem1686867 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1686868 (a : real) (u : real) (x : real) (y : real) (b : real) : (term176 a u x y b) = (term177 a u x y b).
Proof. exact (@lem1686867 (term153 a u x y b)). Qed.
Lemma lem1686869 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term178 a u x y b v) = (term152 a u x v y b).
Proof. exact (eq_refl (term178 a u x y b v)). Qed.
Lemma lem1686870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686871 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term179 a u x y b v) = (term171 a u x v y b).
Proof. exact (MK_COMB (@lem1686870) (@lem1686869 a u x v y b)). Qed.
Lemma lem1686872 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term179 a u x y b v) = (term170 a u x v y b).
Proof. exact (TRANS (@lem1686871 a u x v y b) (@lem1686866 a u x v y b)). Qed.
Lemma lem1686873 (a : real) (u : real) (x : real) (y : real) (b : real) : (term180 a u x y b) = (term181 a u x y b).
Proof. exact (fun_ext (fun v : real => @lem1686872 a u x v y b)). Qed.
Lemma lem1686874 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1686875 (a : real) (u : real) (x : real) (y : real) (b : real) : (term177 a u x y b) = (term182 a u x y b).
Proof. exact (MK_COMB (@lem1686874) (@lem1686873 a u x y b)). Qed.
Lemma lem1686876 (a : real) (u : real) (x : real) (y : real) (b : real) : (term176 a u x y b) = (term182 a u x y b).
Proof. exact (TRANS (@lem1686868 a u x y b) (@lem1686875 a u x y b)). Qed.
Lemma lem1686877 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1686878 (a : real) (x : real) (y : real) (b : real) : (term183 a x y b) = (term184 a x y b).
Proof. exact (@lem1686877 (term155 a x y b)). Qed.
Lemma lem1686879 (a : real) (u : real) (x : real) (y : real) (b : real) : (term185 a x y b u) = (term154 a u x y b).
Proof. exact (eq_refl (term185 a x y b u)). Qed.
Lemma lem1686880 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686881 (a : real) (u : real) (x : real) (y : real) (b : real) : (term186 a x y b u) = (term176 a u x y b).
Proof. exact (MK_COMB (@lem1686880) (@lem1686879 a u x y b)). Qed.
Lemma lem1686882 (a : real) (u : real) (x : real) (y : real) (b : real) : (term186 a x y b u) = (term182 a u x y b).
Proof. exact (TRANS (@lem1686881 a u x y b) (@lem1686876 a u x y b)). Qed.
Lemma lem1686883 (a : real) (x : real) (y : real) (b : real) : (term187 a x y b) = (term188 a x y b).
Proof. exact (fun_ext (fun u : real => @lem1686882 a u x y b)). Qed.
Lemma lem1686884 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1686885 (a : real) (x : real) (y : real) (b : real) : (term184 a x y b) = (term189 a x y b).
Proof. exact (MK_COMB (@lem1686884) (@lem1686883 a x y b)). Qed.
Lemma lem1686886 (a : real) (x : real) (y : real) (b : real) : (term183 a x y b) = (term189 a x y b).
Proof. exact (TRANS (@lem1686878 a x y b) (@lem1686885 a x y b)). Qed.
Lemma lem1686887 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1686888 (a : real) (x : real) (y : real) : (term190 a x y) = (term191 a x y).
Proof. exact (@lem1686887 (term157 a x y)). Qed.
Lemma lem1686889 (a : real) (x : real) (y : real) (b : real) : (term192 a x y b) = (term156 a x y b).
Proof. exact (eq_refl (term192 a x y b)). Qed.
Lemma lem1686890 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686891 (a : real) (x : real) (y : real) (b : real) : (term193 a x y b) = (term183 a x y b).
Proof. exact (MK_COMB (@lem1686890) (@lem1686889 a x y b)). Qed.
Lemma lem1686892 (a : real) (x : real) (y : real) (b : real) : (term193 a x y b) = (term189 a x y b).
Proof. exact (TRANS (@lem1686891 a x y b) (@lem1686886 a x y b)). Qed.
Lemma lem1686893 (a : real) (x : real) (y : real) : (term194 a x y) = (term195 a x y).
Proof. exact (fun_ext (fun b : real => @lem1686892 a x y b)). Qed.
Lemma lem1686894 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1686895 (a : real) (x : real) (y : real) : (term191 a x y) = (term196 a x y).
Proof. exact (MK_COMB (@lem1686894) (@lem1686893 a x y)). Qed.
Lemma lem1686896 (a : real) (x : real) (y : real) : (term190 a x y) = (term196 a x y).
Proof. exact (TRANS (@lem1686888 a x y) (@lem1686895 a x y)). Qed.
Lemma lem1686897 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1686898 (x : real) (y : real) : (term197 x y) = (term198 x y).
Proof. exact (@lem1686897 (term159 x y)). Qed.
Lemma lem1686899 (a : real) (x : real) (y : real) : (term199 x y a) = (term158 a x y).
Proof. exact (eq_refl (term199 x y a)). Qed.
Lemma lem1686900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686901 (a : real) (x : real) (y : real) : (term200 x y a) = (term190 a x y).
Proof. exact (MK_COMB (@lem1686900) (@lem1686899 a x y)). Qed.
Lemma lem1686902 (a : real) (x : real) (y : real) : (term200 x y a) = (term196 a x y).
Proof. exact (TRANS (@lem1686901 a x y) (@lem1686896 a x y)). Qed.
Lemma lem1686903 (x : real) (y : real) : (term201 x y) = (term202 x y).
Proof. exact (fun_ext (fun a : real => @lem1686902 a x y)). Qed.
Lemma lem1686904 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1686905 (x : real) (y : real) : (term198 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1686904) (@lem1686903 x y)). Qed.
Lemma lem1686906 (x : real) (y : real) : (term197 x y) = (term203 x y).
Proof. exact (TRANS (@lem1686898 x y) (@lem1686905 x y)). Qed.
Lemma lem1686907 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1686908 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1686907 (term161 x)). Qed.
Lemma lem1686909 (x : real) (y : real) : (term206 x y) = (term160 x y).
Proof. exact (eq_refl (term206 x y)). Qed.
Lemma lem1686910 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686911 (x : real) (y : real) : (term207 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1686910) (@lem1686909 x y)). Qed.
Lemma lem1686912 (x : real) (y : real) : (term207 x y) = (term203 x y).
Proof. exact (TRANS (@lem1686911 x y) (@lem1686906 x y)). Qed.
Lemma lem1686913 (x : real) : (term208 x) = (term209 x).
Proof. exact (fun_ext (fun y : real => @lem1686912 x y)). Qed.
Lemma lem1686914 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1686915 (x : real) : (term205 x) = (term210 x).
Proof. exact (MK_COMB (@lem1686914) (@lem1686913 x)). Qed.
Lemma lem1686916 (x : real) : (term204 x) = (term210 x).
Proof. exact (TRANS (@lem1686908 x) (@lem1686915 x)). Qed.
Lemma lem1686917 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1686918 : term125 = term211.
Proof. exact (@lem1686917 term163). Qed.
Lemma lem1686919 (x : real) : (term212 x) = (term162 x).
Proof. exact (eq_refl (term212 x)). Qed.
Lemma lem1686920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1686921 (x : real) : (term213 x) = (term204 x).
Proof. exact (MK_COMB (@lem1686920) (@lem1686919 x)). Qed.
Lemma lem1686922 (x : real) : (term213 x) = (term210 x).
Proof. exact (TRANS (@lem1686921 x) (@lem1686916 x)). Qed.
Lemma lem1686923 : term214 = term215.
Proof. exact (fun_ext (fun x : real => @lem1686922 x)). Qed.
Lemma lem1686924 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1686925 : term211 = term216.
Proof. exact (MK_COMB (@lem1686924) (@lem1686923)). Qed.
Lemma lem1686998 : term125 = term216.
Proof. exact (TRANS (@lem1686918) (@lem1686925)). Qed.
Lemma lem1686999 (h1 : term125) : term216.
Proof. exact (EQ_MP (@lem1686998) (@lem1686827 h1)). Qed.
Lemma lem1687006 (u : real) (v : real) (a : real) : (term1 u v a) = (term217 u v a).
Proof. exact (@lem17265 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1687007 (u : real) (v : real) : (term149 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1687006 u v a)). Qed.
Lemma lem1687008 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687009 (u : real) (v : real) : (term120 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1687008) (@lem1687007 u v)). Qed.
Lemma lem1687010 (u : real) : (term150 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1687009 u v)). Qed.
Lemma lem1687011 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687012 (u : real) : (term121 u) = (term221 u).
Proof. exact (MK_COMB (@lem1687011) (@lem1687010 u)). Qed.
Lemma lem1687013 : term151 = term222.
Proof. exact (fun_ext (fun u : real => @lem1687012 u)). Qed.
Lemma lem1687014 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687015 : term122 = term223.
Proof. exact (MK_COMB (@lem1687014) (@lem1687013)). Qed.
Lemma lem1687025 {A : Type'} (P : Prop) (Q : A -> Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1687026 (P : Prop) (Q : real -> Prop) : (term226 P Q) = (term227 P Q).
Proof. exact (@lem1687025 real P Q). Qed.
Lemma lem1687027 (u : real) (v : real) : (term228 u v) = (term229 u v).
Proof. exact (@lem1687026 (term52 u v) (term230 u v)). Qed.
Lemma lem1687028 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1687029 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1687030 (u : real) (v : real) (a : real) : (term233 u v a) = (term217 u v a).
Proof. exact (MK_COMB (@lem1687029 u v) (@lem1687028 u v a)). Qed.
Lemma lem1687031 (u : real) (v : real) : (term234 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1687030 u v a)). Qed.
Lemma lem1687032 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687033 (u : real) (v : real) : (term228 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1687032) (@lem1687031 u v)). Qed.
Lemma lem1687034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1687035 (u : real) (v : real) : (term235 u v) = (term236 u v).
Proof. exact (MK_COMB (@lem1687034) (@lem1687033 u v)). Qed.
Lemma lem1687036 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1687037 (u : real) (v : real) : (term237 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1687036 u v a)). Qed.
Lemma lem1687038 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687039 (u : real) (v : real) : (term238 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1687038) (@lem1687037 u v)). Qed.
Lemma lem1687040 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1687041 (u : real) (v : real) : (term229 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1687040 u v) (@lem1687039 u v)). Qed.
Lemma lem1687042 (u : real) (v : real) : ((term228 u v) = (term229 u v)) = ((term219 u v) = (term240 u v)).
Proof. exact (MK_COMB (@lem1687035 u v) (@lem1687041 u v)). Qed.
Lemma lem1687043 (u : real) (v : real) : (term219 u v) = (term240 u v).
Proof. exact (EQ_MP (@lem1687042 u v) (@lem1687027 u v)). Qed.
Lemma lem1687048 (u : real) : (term220 u) = (term241 u).
Proof. exact (fun_ext (fun v : real => @lem1687043 u v)). Qed.
Lemma lem1687049 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687050 (u : real) : (term221 u) = (term242 u).
Proof. exact (MK_COMB (@lem1687049) (@lem1687048 u)). Qed.
Lemma lem1687099 : term222 = term243.
Proof. exact (fun_ext (fun u : real => @lem1687050 u)). Qed.
Lemma lem1687100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687107 : term223 = term244.
Proof. exact (MK_COMB (@lem1687100) (@lem1687099)). Qed.
Lemma lem1687108 : term122 = term244.
Proof. exact (TRANS (@lem1687015) (@lem1687107)). Qed.
Lemma lem1687109 (h1 : term122) : term244.
Proof. exact (EQ_MP (@lem1687108) (@lem1686828 h1)). Qed.
Lemma lem1687119 (u : real) (v : real) : (term245 u v) = (term246 u v).
Proof. exact (@lem17045 (term247 v) ((real_add u v) = term39)). Qed.
Lemma lem1687121 (u : real) : (term248 u) = (term248 u).
Proof. exact (eq_refl (term248 u)). Qed.
Lemma lem1687122 (u : real) (v : real) : (term249 u v) = (term250 u v).
Proof. exact (MK_COMB (@lem1687121 u) (@lem1687119 u v)). Qed.
Lemma lem1687123 (u : real) (v : real) : (term251 u v) = (term249 u v).
Proof. exact (@lem17045 (term247 u) (term252 u v)). Qed.
Lemma lem1687124 (u : real) (v : real) : (term251 u v) = (term250 u v).
Proof. exact (TRANS (@lem1687123 u v) (@lem1687122 u v)). Qed.
Lemma lem1687126 (y : real) (b : real) : (term253 y b) = (term253 y b).
Proof. exact (eq_refl (term253 y b)). Qed.
Lemma lem1687127 (y : real) (b : real) (u : real) (v : real) : (term254 y b u v) = (term255 y b u v).
Proof. exact (MK_COMB (@lem1687126 y b) (@lem1687124 u v)). Qed.
Lemma lem1687128 (y : real) (b : real) (u : real) (v : real) : (term256 y b u v) = (term254 y b u v).
Proof. exact (@lem17045 (real_le y b) (term257 u v)). Qed.
Lemma lem1687129 (y : real) (b : real) (u : real) (v : real) : (term256 y b u v) = (term255 y b u v).
Proof. exact (TRANS (@lem1687128 y b u v) (@lem1687127 y b u v)). Qed.
Lemma lem1687131 (x : real) (a : real) : (term253 x a) = (term253 x a).
Proof. exact (eq_refl (term253 x a)). Qed.
Lemma lem1687132 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term258 x a y b u v) = (term259 x a y b u v).
Proof. exact (MK_COMB (@lem1687131 x a) (@lem1687129 y b u v)). Qed.
Lemma lem1687133 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term260 x a y b u v) = (term258 x a y b u v).
Proof. exact (@lem17045 (real_le x a) (term261 y b u v)). Qed.
Lemma lem1687134 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term260 x a y b u v) = (term259 x a y b u v).
Proof. exact (TRANS (@lem1687133 x a y b u v) (@lem1687132 x a y b u v)). Qed.
Lemma lem1687135 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term262 x y u a v b) = (term262 x y u a v b).
Proof. exact (eq_refl (term262 x y u a v b)). Qed.
Lemma lem1687136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1687137 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term263 x a y b u v) = (term264 x a y b u v).
Proof. exact (MK_COMB (@lem1687136) (@lem1687134 x a y b u v)). Qed.
Lemma lem1687138 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term265 x y u a v b) = (term266 x y u a v b).
Proof. exact (MK_COMB (@lem1687137 x a y b u v) (@lem1687135 x y u a v b)). Qed.
Lemma lem1687139 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term265 x y u a v b).
Proof. exact (@lem17265 (term267 x a y b u v) (term262 x y u a v b)). Qed.
Lemma lem1687140 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term266 x y u a v b).
Proof. exact (TRANS (@lem1687139 x y u a v b) (@lem1687138 x y u a v b)). Qed.
Lemma lem1687141 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1687140 x y u a v b)). Qed.
Lemma lem1687142 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687143 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1687142) (@lem1687141 x y u a b)). Qed.
Lemma lem1687144 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1687143 x y u a b)). Qed.
Lemma lem1687145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687146 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1687145) (@lem1687144 x y a b)). Qed.
Lemma lem1687147 (x : real) (y : real) (b : real) : (term142 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1687146 x y a b)). Qed.
Lemma lem1687148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687149 (x : real) (y : real) (b : real) : (term143 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1687148) (@lem1687147 x y b)). Qed.
Lemma lem1687150 (x : real) (b : real) : (term144 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1687149 x y b)). Qed.
Lemma lem1687151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687152 (x : real) (b : real) : (term145 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1687151) (@lem1687150 x b)). Qed.
Lemma lem1687153 (b : real) : (term146 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1687152 x b)). Qed.
Lemma lem1687154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687155 (b : real) : (term147 b) = (term277 b).
Proof. exact (MK_COMB (@lem1687154) (@lem1687153 b)). Qed.
Lemma lem1687156 : term148 = term278.
Proof. exact (fun_ext (fun b : real => @lem1687155 b)). Qed.
Lemma lem1687157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687230 : term119 = term279.
Proof. exact (MK_COMB (@lem1687157) (@lem1687156)). Qed.
Lemma lem1687231 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1687230) (@lem1686829 h1)). Qed.
Lemma lem1687232 (x : real) (h1 : term210 x) : term210 x.
Proof. exact (h1). Qed.
Lemma lem1687233 (x : real) (y : real) (h1 : term203 x y) : term203 x y.
Proof. exact (h1). Qed.
Lemma lem1687234 (a : real) (x : real) (y : real) (h1 : term196 a x y) : term196 a x y.
Proof. exact (h1). Qed.
Lemma lem1687235 (a : real) (x : real) (y : real) (b : real) (h1 : term189 a x y b) : term189 a x y b.
Proof. exact (h1). Qed.
Lemma lem1687236 (a : real) (u : real) (x : real) (y : real) (b : real) (h1 : term182 a u x y b) : term182 a u x y b.
Proof. exact (h1). Qed.
Lemma lem1687254 (u : real) (v : real) (a : real) : ((term31 u v a) = a) = ((term31 u v a) = a).
Proof. exact (eq_refl ((term31 u v a) = a)). Qed.
Lemma lem1687255 (u : real) (v : real) : (term230 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1687254 u v a)). Qed.
Lemma lem1687256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687257 (u : real) (v : real) : (term239 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1687256) (@lem1687255 u v)). Qed.
Lemma lem1687276 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1687277 (u : real) (v : real) : (term240 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1687276 u v) (@lem1687257 u v)). Qed.
Lemma lem1687278 (u : real) : (term241 u) = (term241 u).
Proof. exact (fun_ext (fun v : real => @lem1687277 u v)). Qed.
Lemma lem1687279 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687280 (u : real) : (term242 u) = (term242 u).
Proof. exact (MK_COMB (@lem1687279) (@lem1687278 u)). Qed.
Lemma lem1687281 : term243 = term243.
Proof. exact (fun_ext (fun u : real => @lem1687280 u)). Qed.
Lemma lem1687282 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687283 : term244 = term244.
Proof. exact (MK_COMB (@lem1687282) (@lem1687281)). Qed.
Lemma lem1687284 (h1 : term122) : term244.
Proof. exact (EQ_MP (@lem1687283) (@lem1687109 h1)). Qed.
Lemma lem1687381 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term266 x y u a v b) = (term266 x y u a v b).
Proof. exact (eq_refl (term266 x y u a v b)). Qed.
Lemma lem1687382 (x : real) (y : real) (u : real) (a : real) (b : real) : (term268 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1687381 x y u a v b)). Qed.
Lemma lem1687383 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687384 (x : real) (y : real) (u : real) (a : real) (b : real) : (term269 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1687383) (@lem1687382 x y u a b)). Qed.
Lemma lem1687385 (x : real) (y : real) (a : real) (b : real) : (term270 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1687384 x y u a b)). Qed.
Lemma lem1687386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687387 (x : real) (y : real) (a : real) (b : real) : (term271 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1687386) (@lem1687385 x y a b)). Qed.
Lemma lem1687388 (x : real) (y : real) (b : real) : (term272 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1687387 x y a b)). Qed.
Lemma lem1687389 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687390 (x : real) (y : real) (b : real) : (term273 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1687389) (@lem1687388 x y b)). Qed.
Lemma lem1687391 (x : real) (b : real) : (term274 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1687390 x y b)). Qed.
Lemma lem1687392 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687393 (x : real) (b : real) : (term275 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1687392) (@lem1687391 x b)). Qed.
Lemma lem1687394 (b : real) : (term276 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1687393 x b)). Qed.
Lemma lem1687395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687396 (b : real) : (term277 b) = (term277 b).
Proof. exact (MK_COMB (@lem1687395) (@lem1687394 b)). Qed.
Lemma lem1687397 : term278 = term278.
Proof. exact (fun_ext (fun b : real => @lem1687396 b)). Qed.
Lemma lem1687398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687399 : term279 = term279.
Proof. exact (MK_COMB (@lem1687398) (@lem1687397)). Qed.
Lemma lem1687400 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1687399) (@lem1687231 h1)). Qed.
Lemma lem1687516 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term170 a u x v y b.
Proof. exact (h1). Qed.
Lemma lem1687517 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term165 a u x v y b.
Proof. exact (proj2 (@lem1687516 a u x v y b h1)). Qed.
Lemma lem1687518 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term172 x a y b u v.
Proof. exact (proj1 (@lem1687516 a u x v y b h1)). Qed.
Lemma lem1687519 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term280 x a y b u v.
Proof. exact (proj2 (@lem1687518 a u x v y b h1)). Qed.
Lemma lem1687521 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term281 a y b u v.
Proof. exact (proj2 (@lem1687519 a u x v y b h1)). Qed.
Lemma lem1687523 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term261 y b u v.
Proof. exact (proj2 (@lem1687521 a u x v y b h1)). Qed.
Lemma lem1687525 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term257 u v.
Proof. exact (proj2 (@lem1687523 a u x v y b h1)). Qed.
Lemma lem1687527 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term252 u v.
Proof. exact (proj2 (@lem1687525 a u x v y b h1)). Qed.
Lemma lem1687534 {A : Type'} (P : Prop) (Q : A -> Prop) : (term225 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1687535 (P : Prop) (Q : real -> Prop) : (term227 P Q) = (term226 P Q).
Proof. exact (@lem1687534 real P Q). Qed.
Lemma lem1687536 (u : real) (v : real) : (term229 u v) = (term228 u v).
Proof. exact (@lem1687535 (term52 u v) (term230 u v)). Qed.
Lemma lem1687537 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1687538 (u : real) (v : real) : (term237 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1687537 u v a)). Qed.
Lemma lem1687539 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687540 (u : real) (v : real) : (term238 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1687539) (@lem1687538 u v)). Qed.
Lemma lem1687541 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1687542 (u : real) (v : real) : (term229 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1687541 u v) (@lem1687540 u v)). Qed.
Lemma lem1687543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1687544 (u : real) (v : real) : (term282 u v) = (term283 u v).
Proof. exact (MK_COMB (@lem1687543) (@lem1687542 u v)). Qed.
Lemma lem1687545 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1687546 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1687547 (u : real) (v : real) (a : real) : (term233 u v a) = (term217 u v a).
Proof. exact (MK_COMB (@lem1687546 u v) (@lem1687545 u v a)). Qed.
Lemma lem1687548 (u : real) (v : real) : (term234 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1687547 u v a)). Qed.
Lemma lem1687549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687550 (u : real) (v : real) : (term228 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1687549) (@lem1687548 u v)). Qed.
Lemma lem1687551 (u : real) (v : real) : ((term229 u v) = (term228 u v)) = ((term240 u v) = (term219 u v)).
Proof. exact (MK_COMB (@lem1687544 u v) (@lem1687550 u v)). Qed.
Lemma lem1687552 (u : real) (v : real) : (term240 u v) = (term219 u v).
Proof. exact (EQ_MP (@lem1687551 u v) (@lem1687536 u v)). Qed.
Lemma lem1687553 (u : real) : (term241 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1687552 u v)). Qed.
Lemma lem1687554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687555 (u : real) : (term242 u) = (term221 u).
Proof. exact (MK_COMB (@lem1687554) (@lem1687553 u)). Qed.
Lemma lem1687556 : term243 = term222.
Proof. exact (fun_ext (fun u : real => @lem1687555 u)). Qed.
Lemma lem1687557 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687558 : term244 = term223.
Proof. exact (MK_COMB (@lem1687557) (@lem1687556)). Qed.
Lemma lem1687565 (u : real) (v : real) (a : real) : (term217 u v a) = (term217 u v a).
Proof. exact (eq_refl (term217 u v a)). Qed.
Lemma lem1687566 (u : real) (v : real) : (term218 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1687565 u v a)). Qed.
Lemma lem1687567 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687568 (u : real) (v : real) : (term219 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1687567) (@lem1687566 u v)). Qed.
Lemma lem1687569 (u : real) : (term220 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1687568 u v)). Qed.
Lemma lem1687570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687571 (u : real) : (term221 u) = (term221 u).
Proof. exact (MK_COMB (@lem1687570) (@lem1687569 u)). Qed.
Lemma lem1687572 : term222 = term222.
Proof. exact (fun_ext (fun u : real => @lem1687571 u)). Qed.
Lemma lem1687573 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687574 : term223 = term223.
Proof. exact (MK_COMB (@lem1687573) (@lem1687572)). Qed.
Lemma lem1687575 : term244 = term223.
Proof. exact (TRANS (@lem1687558) (@lem1687574)). Qed.
Lemma lem1687576 (h1 : term122) : term223.
Proof. exact (EQ_MP (@lem1687575) (@lem1687284 h1)). Qed.
Lemma lem1687608 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term266 x y u a v b) = (term266 x y u a v b).
Proof. exact (eq_refl (term266 x y u a v b)). Qed.
Lemma lem1687609 (x : real) (y : real) (u : real) (a : real) (b : real) : (term268 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1687608 x y u a v b)). Qed.
Lemma lem1687610 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687611 (x : real) (y : real) (u : real) (a : real) (b : real) : (term269 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1687610) (@lem1687609 x y u a b)). Qed.
Lemma lem1687612 (x : real) (y : real) (a : real) (b : real) : (term270 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1687611 x y u a b)). Qed.
Lemma lem1687613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687614 (x : real) (y : real) (a : real) (b : real) : (term271 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1687613) (@lem1687612 x y a b)). Qed.
Lemma lem1687615 (x : real) (y : real) (b : real) : (term272 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1687614 x y a b)). Qed.
Lemma lem1687616 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687617 (x : real) (y : real) (b : real) : (term273 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1687616) (@lem1687615 x y b)). Qed.
Lemma lem1687618 (x : real) (b : real) : (term274 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1687617 x y b)). Qed.
Lemma lem1687619 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687620 (x : real) (b : real) : (term275 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1687619) (@lem1687618 x b)). Qed.
Lemma lem1687621 (b : real) : (term276 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1687620 x b)). Qed.
Lemma lem1687622 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687623 (b : real) : (term277 b) = (term277 b).
Proof. exact (MK_COMB (@lem1687622) (@lem1687621 b)). Qed.
Lemma lem1687624 : term278 = term278.
Proof. exact (fun_ext (fun b : real => @lem1687623 b)). Qed.
Lemma lem1687625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687627 : term279 = term279.
Proof. exact (MK_COMB (@lem1687625) (@lem1687624)). Qed.
Lemma lem1687628 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1687627) (@lem1687400 h1)). Qed.
Lemma lem1687660 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term284 a u x v y) : term284 a u x v y.
Proof. exact (h1). Qed.
Lemma lem1687662 {A : Type'} (P : Prop) (Q : A -> Prop) : (term225 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1687663 (P : Prop) (Q : real -> Prop) : (term227 P Q) = (term226 P Q).
Proof. exact (@lem1687662 real P Q). Qed.
Lemma lem1687664 (u : real) (v : real) : (term229 u v) = (term228 u v).
Proof. exact (@lem1687663 (term52 u v) (term230 u v)). Qed.
Lemma lem1687665 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1687666 (u : real) (v : real) : (term237 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1687665 u v a)). Qed.
Lemma lem1687667 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687668 (u : real) (v : real) : (term238 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1687667) (@lem1687666 u v)). Qed.
Lemma lem1687669 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1687670 (u : real) (v : real) : (term229 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1687669 u v) (@lem1687668 u v)). Qed.
Lemma lem1687671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1687672 (u : real) (v : real) : (term282 u v) = (term283 u v).
Proof. exact (MK_COMB (@lem1687671) (@lem1687670 u v)). Qed.
Lemma lem1687673 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1687674 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1687675 (u : real) (v : real) (a : real) : (term233 u v a) = (term217 u v a).
Proof. exact (MK_COMB (@lem1687674 u v) (@lem1687673 u v a)). Qed.
Lemma lem1687676 (u : real) (v : real) : (term234 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1687675 u v a)). Qed.
Lemma lem1687677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687678 (u : real) (v : real) : (term228 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1687677) (@lem1687676 u v)). Qed.
Lemma lem1687679 (u : real) (v : real) : ((term229 u v) = (term228 u v)) = ((term240 u v) = (term219 u v)).
Proof. exact (MK_COMB (@lem1687672 u v) (@lem1687678 u v)). Qed.
Lemma lem1687680 (u : real) (v : real) : (term240 u v) = (term219 u v).
Proof. exact (EQ_MP (@lem1687679 u v) (@lem1687664 u v)). Qed.
Lemma lem1687681 (u : real) : (term241 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1687680 u v)). Qed.
Lemma lem1687682 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687683 (u : real) : (term242 u) = (term221 u).
Proof. exact (MK_COMB (@lem1687682) (@lem1687681 u)). Qed.
Lemma lem1687684 : term243 = term222.
Proof. exact (fun_ext (fun u : real => @lem1687683 u)). Qed.
Lemma lem1687685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687686 : term244 = term223.
Proof. exact (MK_COMB (@lem1687685) (@lem1687684)). Qed.
Lemma lem1687693 (u : real) (v : real) (a : real) : (term217 u v a) = (term217 u v a).
Proof. exact (eq_refl (term217 u v a)). Qed.
Lemma lem1687694 (u : real) (v : real) : (term218 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1687693 u v a)). Qed.
Lemma lem1687695 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687696 (u : real) (v : real) : (term219 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1687695) (@lem1687694 u v)). Qed.
Lemma lem1687697 (u : real) : (term220 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1687696 u v)). Qed.
Lemma lem1687698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687699 (u : real) : (term221 u) = (term221 u).
Proof. exact (MK_COMB (@lem1687698) (@lem1687697 u)). Qed.
Lemma lem1687700 : term222 = term222.
Proof. exact (fun_ext (fun u : real => @lem1687699 u)). Qed.
Lemma lem1687701 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687702 : term223 = term223.
Proof. exact (MK_COMB (@lem1687701) (@lem1687700)). Qed.
Lemma lem1687703 : term244 = term223.
Proof. exact (TRANS (@lem1687686) (@lem1687702)). Qed.
Lemma lem1687704 (h1 : term122) : term223.
Proof. exact (EQ_MP (@lem1687703) (@lem1687284 h1)). Qed.
Lemma lem1687736 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term266 x y u a v b) = (term266 x y u a v b).
Proof. exact (eq_refl (term266 x y u a v b)). Qed.
Lemma lem1687737 (x : real) (y : real) (u : real) (a : real) (b : real) : (term268 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1687736 x y u a v b)). Qed.
Lemma lem1687738 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687739 (x : real) (y : real) (u : real) (a : real) (b : real) : (term269 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1687738) (@lem1687737 x y u a b)). Qed.
Lemma lem1687740 (x : real) (y : real) (a : real) (b : real) : (term270 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1687739 x y u a b)). Qed.
Lemma lem1687741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687742 (x : real) (y : real) (a : real) (b : real) : (term271 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1687741) (@lem1687740 x y a b)). Qed.
Lemma lem1687743 (x : real) (y : real) (b : real) : (term272 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1687742 x y a b)). Qed.
Lemma lem1687744 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687745 (x : real) (y : real) (b : real) : (term273 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1687744) (@lem1687743 x y b)). Qed.
Lemma lem1687746 (x : real) (b : real) : (term274 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1687745 x y b)). Qed.
Lemma lem1687747 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687748 (x : real) (b : real) : (term275 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1687747) (@lem1687746 x b)). Qed.
Lemma lem1687749 (b : real) : (term276 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1687748 x b)). Qed.
Lemma lem1687750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687751 (b : real) : (term277 b) = (term277 b).
Proof. exact (MK_COMB (@lem1687750) (@lem1687749 b)). Qed.
Lemma lem1687752 : term278 = term278.
Proof. exact (fun_ext (fun b : real => @lem1687751 b)). Qed.
Lemma lem1687753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1687755 : term279 = term279.
Proof. exact (MK_COMB (@lem1687753) (@lem1687752)). Qed.
Lemma lem1687756 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1687755) (@lem1687400 h1)). Qed.
Lemma lem1687788 (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term285 u x v y b) : term285 u x v y b.
Proof. exact (h1). Qed.
Lemma lem1687789 (_26023 : real) (h1 : term122) : term286 _26023.
Proof. exact (@lem1687576 h1 _26023). Qed.
Lemma lem1687790 (_26023 : real) : (term286 _26023) = (term221 _26023).
Proof. exact (eq_refl (term286 _26023)). Qed.
Lemma lem1687791 (_26023 : real) (h1 : term122) : term221 _26023.
Proof. exact (EQ_MP (@lem1687790 _26023) (@lem1687789 _26023 h1)). Qed.
Lemma lem1687792 (_26023 : real) (_26024 : real) (h1 : term122) : term287 _26023 _26024.
Proof. exact (@lem1687791 _26023 h1 _26024). Qed.
Lemma lem1687793 (_26023 : real) (_26024 : real) : (term287 _26023 _26024) = (term219 _26023 _26024).
Proof. exact (eq_refl (term287 _26023 _26024)). Qed.
Lemma lem1687794 (_26023 : real) (_26024 : real) (h1 : term122) : term219 _26023 _26024.
Proof. exact (EQ_MP (@lem1687793 _26023 _26024) (@lem1687792 _26023 _26024 h1)). Qed.
Lemma lem1687795 (_26023 : real) (_26024 : real) (_26025 : real) (h1 : term122) : term288 _26023 _26024 _26025.
Proof. exact (@lem1687794 _26023 _26024 h1 _26025). Qed.
Lemma lem1687796 (_26023 : real) (_26024 : real) (_26025 : real) : (term288 _26023 _26024 _26025) = (term217 _26023 _26024 _26025).
Proof. exact (eq_refl (term288 _26023 _26024 _26025)). Qed.
Lemma lem1687798 (_26026 : real) (h1 : term119) : term289 _26026.
Proof. exact (@lem1687628 h1 _26026). Qed.
Lemma lem1687799 (_26026 : real) : (term289 _26026) = (term277 _26026).
Proof. exact (eq_refl (term289 _26026)). Qed.
Lemma lem1687800 (_26026 : real) (h1 : term119) : term277 _26026.
Proof. exact (EQ_MP (@lem1687799 _26026) (@lem1687798 _26026 h1)). Qed.
Lemma lem1687801 (_26026 : real) (_26027 : real) (h1 : term119) : term290 _26026 _26027.
Proof. exact (@lem1687800 _26026 h1 _26027). Qed.
Lemma lem1687802 (_26027 : real) (_26026 : real) : (term290 _26026 _26027) = (term275 _26027 _26026).
Proof. exact (eq_refl (term290 _26026 _26027)). Qed.
Lemma lem1687803 (_26027 : real) (_26026 : real) (h1 : term119) : term275 _26027 _26026.
Proof. exact (EQ_MP (@lem1687802 _26027 _26026) (@lem1687801 _26026 _26027 h1)). Qed.
Lemma lem1687804 (_26027 : real) (_26026 : real) (_26028 : real) (h1 : term119) : term291 _26027 _26026 _26028.
Proof. exact (@lem1687803 _26027 _26026 h1 _26028). Qed.
Lemma lem1687805 (_26027 : real) (_26028 : real) (_26026 : real) : (term291 _26027 _26026 _26028) = (term273 _26027 _26028 _26026).
Proof. exact (eq_refl (term291 _26027 _26026 _26028)). Qed.
Lemma lem1687806 (_26027 : real) (_26028 : real) (_26026 : real) (h1 : term119) : term273 _26027 _26028 _26026.
Proof. exact (EQ_MP (@lem1687805 _26027 _26028 _26026) (@lem1687804 _26027 _26026 _26028 h1)). Qed.
Lemma lem1687807 (_26027 : real) (_26028 : real) (_26026 : real) (_26029 : real) (h1 : term119) : term292 _26027 _26028 _26026 _26029.
Proof. exact (@lem1687806 _26027 _26028 _26026 h1 _26029). Qed.
Lemma lem1687808 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) : (term292 _26027 _26028 _26026 _26029) = (term271 _26027 _26028 _26029 _26026).
Proof. exact (eq_refl (term292 _26027 _26028 _26026 _26029)). Qed.
Lemma lem1687809 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (h1 : term119) : term271 _26027 _26028 _26029 _26026.
Proof. exact (EQ_MP (@lem1687808 _26027 _26028 _26029 _26026) (@lem1687807 _26027 _26028 _26026 _26029 h1)). Qed.
Lemma lem1687810 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (h1 : term119) : term293 _26027 _26028 _26029 _26026 _26030.
Proof. exact (@lem1687809 _26027 _26028 _26029 _26026 h1 _26030). Qed.
Lemma lem1687811 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26026 : real) : (term293 _26027 _26028 _26029 _26026 _26030) = (term269 _26027 _26028 _26030 _26029 _26026).
Proof. exact (eq_refl (term293 _26027 _26028 _26029 _26026 _26030)). Qed.
Lemma lem1687812 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26026 : real) (h1 : term119) : term269 _26027 _26028 _26030 _26029 _26026.
Proof. exact (EQ_MP (@lem1687811 _26027 _26028 _26030 _26029 _26026) (@lem1687810 _26027 _26028 _26029 _26026 _26030 h1)). Qed.
Lemma lem1687813 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26026 : real) (_26031 : real) (h1 : term119) : term294 _26027 _26028 _26030 _26029 _26026 _26031.
Proof. exact (@lem1687812 _26027 _26028 _26030 _26029 _26026 h1 _26031). Qed.
Lemma lem1687814 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term294 _26027 _26028 _26030 _26029 _26026 _26031) = (term266 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (eq_refl (term294 _26027 _26028 _26030 _26029 _26026 _26031)). Qed.
Lemma lem1687815 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) (h1 : term119) : term266 _26027 _26028 _26030 _26029 _26031 _26026.
Proof. exact (EQ_MP (@lem1687814 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1687813 _26027 _26028 _26030 _26029 _26026 _26031 h1)). Qed.
Lemma lem1687816 (_26032 : real) (h1 : term122) : term286 _26032.
Proof. exact (@lem1687704 h1 _26032). Qed.
Lemma lem1687817 (_26032 : real) : (term286 _26032) = (term221 _26032).
Proof. exact (eq_refl (term286 _26032)). Qed.
Lemma lem1687818 (_26032 : real) (h1 : term122) : term221 _26032.
Proof. exact (EQ_MP (@lem1687817 _26032) (@lem1687816 _26032 h1)). Qed.
Lemma lem1687819 (_26032 : real) (_26033 : real) (h1 : term122) : term287 _26032 _26033.
Proof. exact (@lem1687818 _26032 h1 _26033). Qed.
Lemma lem1687820 (_26032 : real) (_26033 : real) : (term287 _26032 _26033) = (term219 _26032 _26033).
Proof. exact (eq_refl (term287 _26032 _26033)). Qed.
Lemma lem1687821 (_26032 : real) (_26033 : real) (h1 : term122) : term219 _26032 _26033.
Proof. exact (EQ_MP (@lem1687820 _26032 _26033) (@lem1687819 _26032 _26033 h1)). Qed.
Lemma lem1687822 (_26032 : real) (_26033 : real) (_26034 : real) (h1 : term122) : term288 _26032 _26033 _26034.
Proof. exact (@lem1687821 _26032 _26033 h1 _26034). Qed.
Lemma lem1687823 (_26032 : real) (_26033 : real) (_26034 : real) : (term288 _26032 _26033 _26034) = (term217 _26032 _26033 _26034).
Proof. exact (eq_refl (term288 _26032 _26033 _26034)). Qed.
Lemma lem1687825 (_26035 : real) (h1 : term119) : term289 _26035.
Proof. exact (@lem1687756 h1 _26035). Qed.
Lemma lem1687826 (_26035 : real) : (term289 _26035) = (term277 _26035).
Proof. exact (eq_refl (term289 _26035)). Qed.
Lemma lem1687827 (_26035 : real) (h1 : term119) : term277 _26035.
Proof. exact (EQ_MP (@lem1687826 _26035) (@lem1687825 _26035 h1)). Qed.
Lemma lem1687828 (_26035 : real) (_26036 : real) (h1 : term119) : term290 _26035 _26036.
Proof. exact (@lem1687827 _26035 h1 _26036). Qed.
Lemma lem1687829 (_26036 : real) (_26035 : real) : (term290 _26035 _26036) = (term275 _26036 _26035).
Proof. exact (eq_refl (term290 _26035 _26036)). Qed.
Lemma lem1687830 (_26036 : real) (_26035 : real) (h1 : term119) : term275 _26036 _26035.
Proof. exact (EQ_MP (@lem1687829 _26036 _26035) (@lem1687828 _26035 _26036 h1)). Qed.
Lemma lem1687831 (_26036 : real) (_26035 : real) (_26037 : real) (h1 : term119) : term291 _26036 _26035 _26037.
Proof. exact (@lem1687830 _26036 _26035 h1 _26037). Qed.
Lemma lem1687832 (_26036 : real) (_26037 : real) (_26035 : real) : (term291 _26036 _26035 _26037) = (term273 _26036 _26037 _26035).
Proof. exact (eq_refl (term291 _26036 _26035 _26037)). Qed.
Lemma lem1687833 (_26036 : real) (_26037 : real) (_26035 : real) (h1 : term119) : term273 _26036 _26037 _26035.
Proof. exact (EQ_MP (@lem1687832 _26036 _26037 _26035) (@lem1687831 _26036 _26035 _26037 h1)). Qed.
Lemma lem1687834 (_26036 : real) (_26037 : real) (_26035 : real) (_26038 : real) (h1 : term119) : term292 _26036 _26037 _26035 _26038.
Proof. exact (@lem1687833 _26036 _26037 _26035 h1 _26038). Qed.
Lemma lem1687835 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) : (term292 _26036 _26037 _26035 _26038) = (term271 _26036 _26037 _26038 _26035).
Proof. exact (eq_refl (term292 _26036 _26037 _26035 _26038)). Qed.
Lemma lem1687836 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (h1 : term119) : term271 _26036 _26037 _26038 _26035.
Proof. exact (EQ_MP (@lem1687835 _26036 _26037 _26038 _26035) (@lem1687834 _26036 _26037 _26035 _26038 h1)). Qed.
Lemma lem1687837 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (h1 : term119) : term293 _26036 _26037 _26038 _26035 _26039.
Proof. exact (@lem1687836 _26036 _26037 _26038 _26035 h1 _26039). Qed.
Lemma lem1687838 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26035 : real) : (term293 _26036 _26037 _26038 _26035 _26039) = (term269 _26036 _26037 _26039 _26038 _26035).
Proof. exact (eq_refl (term293 _26036 _26037 _26038 _26035 _26039)). Qed.
Lemma lem1687839 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26035 : real) (h1 : term119) : term269 _26036 _26037 _26039 _26038 _26035.
Proof. exact (EQ_MP (@lem1687838 _26036 _26037 _26039 _26038 _26035) (@lem1687837 _26036 _26037 _26038 _26035 _26039 h1)). Qed.
Lemma lem1687840 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26035 : real) (_26040 : real) (h1 : term119) : term294 _26036 _26037 _26039 _26038 _26035 _26040.
Proof. exact (@lem1687839 _26036 _26037 _26039 _26038 _26035 h1 _26040). Qed.
Lemma lem1687841 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term294 _26036 _26037 _26039 _26038 _26035 _26040) = (term266 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (eq_refl (term294 _26036 _26037 _26039 _26038 _26035 _26040)). Qed.
Lemma lem1687842 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) (h1 : term119) : term266 _26036 _26037 _26039 _26038 _26040 _26035.
Proof. exact (EQ_MP (@lem1687841 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1687840 _26036 _26037 _26039 _26038 _26035 _26040 h1)). Qed.
Lemma lem1687848 (_26023 : real) (_26024 : real) (_26025 : real) (h1 : term122) : term217 _26023 _26024 _26025.
Proof. exact (EQ_MP (@lem1687796 _26023 _26024 _26025) (@lem1687795 _26023 _26024 _26025 h1)). Qed.
Lemma lem1687852 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term266 _26027 _26028 _26030 _26029 _26031 _26026) = (term295 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (@lem1686455 (term296 _26027 _26029) (term255 _26028 _26026 _26030 _26031) (term262 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687853 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term297 _26027 _26028 _26030 _26029 _26031 _26026) = (term298 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (@lem1686455 (term296 _26028 _26026) (term250 _26030 _26031) (term262 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687854 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term299 _26027 _26028 _26030 _26029 _26031 _26026) = (term300 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (@lem1686455 (term301 _26030) (term246 _26030 _26031) (term262 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687861 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term302 _26027 _26028 _26030 _26029 _26031 _26026) = (term303 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (@lem1686455 (term301 _26031) (term52 _26030 _26031) (term262 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687862 (_26030 : real) : (term248 _26030) = (term248 _26030).
Proof. exact (eq_refl (term248 _26030)). Qed.
Lemma lem1687865 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term300 _26027 _26028 _26030 _26029 _26031 _26026) = (term304 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (MK_COMB (@lem1687862 _26030) (@lem1687861 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687866 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term299 _26027 _26028 _26030 _26029 _26031 _26026) = (term304 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (TRANS (@lem1687854 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1687865 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687867 (_26028 : real) (_26026 : real) : (term253 _26028 _26026) = (term253 _26028 _26026).
Proof. exact (eq_refl (term253 _26028 _26026)). Qed.
Lemma lem1687870 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term298 _26027 _26028 _26030 _26029 _26031 _26026) = (term305 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (MK_COMB (@lem1687867 _26028 _26026) (@lem1687866 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687871 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term297 _26027 _26028 _26030 _26029 _26031 _26026) = (term305 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (TRANS (@lem1687853 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1687870 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687872 (_26027 : real) (_26029 : real) : (term253 _26027 _26029) = (term253 _26027 _26029).
Proof. exact (eq_refl (term253 _26027 _26029)). Qed.
Lemma lem1687875 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term295 _26027 _26028 _26030 _26029 _26031 _26026) = (term306 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (MK_COMB (@lem1687872 _26027 _26029) (@lem1687871 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687877 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term266 _26027 _26028 _26030 _26029 _26031 _26026) = (term306 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (TRANS (@lem1687852 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1687875 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1687878 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) (h1 : term119) : term306 _26027 _26028 _26030 _26029 _26031 _26026.
Proof. exact (EQ_MP (@lem1687877 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1687815 _26027 _26028 _26030 _26029 _26031 _26026 h1)). Qed.
Lemma lem1687894 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term284 a u x v y) : term284 a u x v y.
Proof. exact (h1). Qed.
Lemma lem1687900 (_26032 : real) (_26033 : real) (_26034 : real) (h1 : term122) : term217 _26032 _26033 _26034.
Proof. exact (EQ_MP (@lem1687823 _26032 _26033 _26034) (@lem1687822 _26032 _26033 _26034 h1)). Qed.
Lemma lem1687904 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term266 _26036 _26037 _26039 _26038 _26040 _26035) = (term295 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (@lem1686455 (term296 _26036 _26038) (term255 _26037 _26035 _26039 _26040) (term262 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687905 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term297 _26036 _26037 _26039 _26038 _26040 _26035) = (term298 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (@lem1686455 (term296 _26037 _26035) (term250 _26039 _26040) (term262 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687906 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term299 _26036 _26037 _26039 _26038 _26040 _26035) = (term300 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (@lem1686455 (term301 _26039) (term246 _26039 _26040) (term262 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687913 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term302 _26036 _26037 _26039 _26038 _26040 _26035) = (term303 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (@lem1686455 (term301 _26040) (term52 _26039 _26040) (term262 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687914 (_26039 : real) : (term248 _26039) = (term248 _26039).
Proof. exact (eq_refl (term248 _26039)). Qed.
Lemma lem1687917 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term300 _26036 _26037 _26039 _26038 _26040 _26035) = (term304 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (MK_COMB (@lem1687914 _26039) (@lem1687913 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687918 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term299 _26036 _26037 _26039 _26038 _26040 _26035) = (term304 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (TRANS (@lem1687906 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1687917 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687919 (_26037 : real) (_26035 : real) : (term253 _26037 _26035) = (term253 _26037 _26035).
Proof. exact (eq_refl (term253 _26037 _26035)). Qed.
Lemma lem1687922 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term298 _26036 _26037 _26039 _26038 _26040 _26035) = (term305 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (MK_COMB (@lem1687919 _26037 _26035) (@lem1687918 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687923 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term297 _26036 _26037 _26039 _26038 _26040 _26035) = (term305 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (TRANS (@lem1687905 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1687922 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687924 (_26036 : real) (_26038 : real) : (term253 _26036 _26038) = (term253 _26036 _26038).
Proof. exact (eq_refl (term253 _26036 _26038)). Qed.
Lemma lem1687927 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term295 _26036 _26037 _26039 _26038 _26040 _26035) = (term306 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (MK_COMB (@lem1687924 _26036 _26038) (@lem1687923 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687929 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term266 _26036 _26037 _26039 _26038 _26040 _26035) = (term306 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (TRANS (@lem1687904 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1687927 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1687930 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) (h1 : term119) : term306 _26036 _26037 _26039 _26038 _26040 _26035.
Proof. exact (EQ_MP (@lem1687929 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1687842 _26036 _26037 _26039 _26038 _26040 _26035 h1)). Qed.
Lemma lem1687946 (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term285 u x v y b) : term285 u x v y b.
Proof. exact (h1). Qed.
Lemma lem1687947 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1687948 (_26041 : real) (_26043 : real) (h1 : _26041 = _26043) : _26041 = _26043.
Proof. exact (h1). Qed.
Lemma lem1687949 (_26042 : real) (_26044 : real) (h1 : _26042 = _26044) : _26042 = _26044.
Proof. exact (h1). Qed.
Lemma lem1687950 (_26041 : real) (_26043 : real) (h1 : _26041 = _26043) : (real_le _26041) = (real_le _26043).
Proof. exact (MK_COMB (@lem1687947) (@lem1687948 _26041 _26043 h1)). Qed.
Lemma lem1687951 (_26041 : real) (_26043 : real) (_26042 : real) (_26044 : real) (h1 : _26041 = _26043) (h2 : _26042 = _26044) : (real_le _26041 _26042) = (real_le _26043 _26044).
Proof. exact (MK_COMB (@lem1687950 _26041 _26043 h1) (@lem1687949 _26042 _26044 h2)). Qed.
Lemma lem1687953 (b : Prop) (a : Prop) : term307 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1687954 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : term308 _26043 _26044 _26041 _26042.
Proof. exact (@lem1687953 (real_le _26043 _26044) (real_le _26041 _26042)). Qed.
Lemma lem1687955 (_26041 : real) (_26043 : real) (_26042 : real) (_26044 : real) (h1 : _26041 = _26043) (h2 : _26042 = _26044) : term309 _26043 _26044 _26041 _26042.
Proof. exact (@lem1687954 _26043 _26044 _26041 _26042 (@lem1687951 _26041 _26043 _26042 _26044 h1 h2)). Qed.
Lemma lem1687956 (_26044 : real) (_26042 : real) (_26041 : real) (_26043 : real) (h1 : _26041 = _26043) : term310 _26043 _26044 _26041 _26042.
Proof. exact (fun h0 : _26042 = _26044 => @lem1687955 _26041 _26043 _26042 _26044 h1 h0). Qed.
Lemma lem1687958 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1687959 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term310 _26043 _26044 _26041 _26042) = (term311 _26043 _26044 _26041 _26042).
Proof. exact (@lem1687958 (_26042 = _26044) (term309 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1687960 (_26044 : real) (_26042 : real) (_26041 : real) (_26043 : real) (h1 : _26041 = _26043) : term311 _26043 _26044 _26041 _26042.
Proof. exact (EQ_MP (@lem1687959 _26043 _26044 _26041 _26042) (@lem1687956 _26044 _26042 _26041 _26043 h1)). Qed.
Lemma lem1687961 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : term312 _26043 _26044 _26041 _26042.
Proof. exact (fun h0 : _26041 = _26043 => @lem1687960 _26044 _26042 _26041 _26043 h0). Qed.
Lemma lem1687963 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1687964 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term312 _26043 _26044 _26041 _26042) = (term313 _26043 _26044 _26041 _26042).
Proof. exact (@lem1687963 (_26041 = _26043) (term311 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1687965 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : term313 _26043 _26044 _26041 _26042.
Proof. exact (EQ_MP (@lem1687964 _26043 _26044 _26041 _26042) (@lem1687961 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688025 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1687527 a u x v y b h1)). Qed.
Lemma lem1688026 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1688025 a u x v y b h1). Qed.
Lemma lem1688028 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688029 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1688028 ((real_add u v) = term39)). Qed.
Lemma lem1688030 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1688029 u v) (@lem1688026 a u x v y b h1)). Qed.
Lemma lem1688036 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1688037 (_26025 : real) (_26023 : real) (_26024 : real) : (term217 _26023 _26024 _26025) = (term314 _26025 _26023 _26024).
Proof. exact (@lem1688036 ((term31 _26023 _26024 _26025) = _26025) (term52 _26023 _26024)). Qed.
Lemma lem1688047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1688048 (_26025 : real) (_26023 : real) (_26024 : real) : (term315 _26023 _26024 _26025) = (term316 _26025 _26023 _26024).
Proof. exact (MK_COMB (@lem1688047) (@lem1688037 _26025 _26023 _26024)). Qed.
Lemma lem1688058 (_26025 : real) (_26023 : real) (_26024 : real) : (term314 _26025 _26023 _26024) = (term314 _26025 _26023 _26024).
Proof. exact (eq_refl (term314 _26025 _26023 _26024)). Qed.
Lemma lem1688059 (_26025 : real) (_26023 : real) (_26024 : real) : ((term217 _26023 _26024 _26025) = (term314 _26025 _26023 _26024)) = ((term314 _26025 _26023 _26024) = (term314 _26025 _26023 _26024)).
Proof. exact (MK_COMB (@lem1688048 _26025 _26023 _26024) (@lem1688058 _26025 _26023 _26024)). Qed.
Lemma lem1688061 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1688062 (x : Prop) : (x = x) = True.
Proof. exact (@lem1688061 Prop x). Qed.
Lemma lem1688063 (_26025 : real) (_26023 : real) (_26024 : real) : ((term314 _26025 _26023 _26024) = (term314 _26025 _26023 _26024)) = True.
Proof. exact (@lem1688062 (term314 _26025 _26023 _26024)). Qed.
Lemma lem1688064 (_26025 : real) (_26023 : real) (_26024 : real) : ((term217 _26023 _26024 _26025) = (term314 _26025 _26023 _26024)) = True.
Proof. exact (TRANS (@lem1688059 _26025 _26023 _26024) (@lem1688063 _26025 _26023 _26024)). Qed.
Lemma lem1688065 (_26025 : real) (_26023 : real) (_26024 : real) : True = ((term217 _26023 _26024 _26025) = (term314 _26025 _26023 _26024)).
Proof. exact (SYM (@lem1688064 _26025 _26023 _26024)). Qed.
Lemma lem1688066 (_26025 : real) (_26023 : real) (_26024 : real) : (term217 _26023 _26024 _26025) = (term314 _26025 _26023 _26024).
Proof. exact (EQ_MP (@lem1688065 _26025 _26023 _26024) (@lem0)). Qed.
Lemma lem1688067 (_26025 : real) (_26023 : real) (_26024 : real) (h1 : term122) : term314 _26025 _26023 _26024.
Proof. exact (EQ_MP (@lem1688066 _26025 _26023 _26024) (@lem1687848 _26023 _26024 _26025 h1)). Qed.
Lemma lem1688069 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1688070 (_26023 : real) (_26024 : real) (_26025 : real) : (term314 _26025 _26023 _26024) = (term317 _26023 _26024 _26025).
Proof. exact (@lem1688069 (term52 _26023 _26024) ((term31 _26023 _26024 _26025) = _26025)). Qed.
Lemma lem1688072 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688073 (_26023 : real) (_26024 : real) : (term318 _26023 _26024) = ((real_add _26023 _26024) = term39).
Proof. exact (@lem1688072 ((real_add _26023 _26024) = term39)). Qed.
Lemma lem1688074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1688075 (_26023 : real) (_26024 : real) : (term319 _26023 _26024) = (term320 _26023 _26024).
Proof. exact (MK_COMB (@lem1688074) (@lem1688073 _26023 _26024)). Qed.
Lemma lem1688076 (_26023 : real) (_26024 : real) (_26025 : real) : ((term31 _26023 _26024 _26025) = _26025) = ((term31 _26023 _26024 _26025) = _26025).
Proof. exact (eq_refl ((term31 _26023 _26024 _26025) = _26025)). Qed.
Lemma lem1688077 (_26023 : real) (_26024 : real) (_26025 : real) : (term317 _26023 _26024 _26025) = (term1 _26023 _26024 _26025).
Proof. exact (MK_COMB (@lem1688075 _26023 _26024) (@lem1688076 _26023 _26024 _26025)). Qed.
Lemma lem1688078 (_26023 : real) (_26024 : real) (_26025 : real) : (term314 _26025 _26023 _26024) = (term1 _26023 _26024 _26025).
Proof. exact (TRANS (@lem1688070 _26023 _26024 _26025) (@lem1688077 _26023 _26024 _26025)). Qed.
Lemma lem1688081 (_26023 : real) (_26024 : real) (_26025 : real) (h1 : term122) : term1 _26023 _26024 _26025.
Proof. exact (EQ_MP (@lem1688078 _26023 _26024 _26025) (@lem1688067 _26025 _26023 _26024 h1)). Qed.
Lemma lem1688082 (u : real) (v : real) (_26025 : real) (h1 : term122) : term1 u v _26025.
Proof. exact (@lem1688081 u v _26025 h1). Qed.
Lemma lem1688085 (_26025 : real) (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v _26025) = _26025.
Proof. exact (@lem1688082 u v _26025 h1 (@lem1688030 a u x v y b h2)). Qed.
Lemma lem1688086 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v a) = a.
Proof. exact (@lem1688085 a a u x v y b h1 h2). Qed.
Lemma lem1688087 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1688086 a u x v y b h1 h2). Qed.
Lemma lem1688089 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688090 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1688089 ((term31 u v a) = a)). Qed.
Lemma lem1688091 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1688090 u v a) (@lem1688087 a u x v y b h1 h2)). Qed.
Lemma lem1688093 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1688094 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (@lem1688093 (term321 u x v y)). Qed.
Lemma lem1688095 (u : real) (x : real) (v : real) (y : real) : term322 u x v y.
Proof. exact (fun h0 : term323 u x v y => @lem1688094 u x v y). Qed.
Lemma lem1688097 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688098 (u : real) (x : real) (v : real) (y : real) : (term322 u x v y) = ((term321 u x v y) = (term321 u x v y)).
Proof. exact (@lem1688097 ((term321 u x v y) = (term321 u x v y))). Qed.
Lemma lem1688099 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (EQ_MP (@lem1688098 u x v y) (@lem1688095 u x v y)). Qed.
Lemma lem1688101 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le a x.
Proof. exact (proj1 (@lem1687518 a u x v y b h1)). Qed.
Lemma lem1688102 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 a x.
Proof. exact (fun h0 : term296 a x => @lem1688101 a u x v y b h1). Qed.
Lemma lem1688104 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688105 (a : real) (x : real) : (term324 a x) = (real_le a x).
Proof. exact (@lem1688104 (real_le a x)). Qed.
Lemma lem1688106 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le a x.
Proof. exact (EQ_MP (@lem1688105 a x) (@lem1688102 a u x v y b h1)). Qed.
Lemma lem1688108 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le a y.
Proof. exact (proj1 (@lem1687521 a u x v y b h1)). Qed.
Lemma lem1688109 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 a y.
Proof. exact (fun h0 : term296 a y => @lem1688108 a u x v y b h1). Qed.
Lemma lem1688111 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688112 (a : real) (y : real) : (term324 a y) = (real_le a y).
Proof. exact (@lem1688111 (real_le a y)). Qed.
Lemma lem1688113 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le a y.
Proof. exact (EQ_MP (@lem1688112 a y) (@lem1688109 a u x v y b h1)). Qed.
Lemma lem1688115 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (proj1 (@lem1687525 a u x v y b h1)). Qed.
Lemma lem1688116 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 u.
Proof. exact (fun h0 : term301 u => @lem1688115 a u x v y b h1). Qed.
Lemma lem1688118 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688119 (u : real) : (term325 u) = (term247 u).
Proof. exact (@lem1688118 (term247 u)). Qed.
Lemma lem1688120 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (EQ_MP (@lem1688119 u) (@lem1688116 a u x v y b h1)). Qed.
Lemma lem1688122 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (proj1 (@lem1687527 a u x v y b h1)). Qed.
Lemma lem1688123 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 v.
Proof. exact (fun h0 : term301 v => @lem1688122 a u x v y b h1). Qed.
Lemma lem1688125 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688126 (v : real) : (term325 v) = (term247 v).
Proof. exact (@lem1688125 (term247 v)). Qed.
Lemma lem1688127 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (EQ_MP (@lem1688126 v) (@lem1688123 a u x v y b h1)). Qed.
Lemma lem1688129 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1687527 a u x v y b h1)). Qed.
Lemma lem1688130 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1688129 a u x v y b h1). Qed.
Lemma lem1688132 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688133 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1688132 ((real_add u v) = term39)). Qed.
Lemma lem1688134 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1688133 u v) (@lem1688130 a u x v y b h1)). Qed.
Lemma lem1688170 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688171 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term303 _26027 _26028 _26030 _26029 _26031 _26026) = (term326 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (@lem1688170 (term52 _26030 _26031) (term301 _26031) (term262 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688187 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1688188 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26026 : real) (_26031 : real) : (term327 _26027 _26028 _26030 _26029 _26031 _26026) = (term328 _26027 _26028 _26030 _26029 _26026 _26031).
Proof. exact (@lem1688187 (term262 _26027 _26028 _26030 _26029 _26031 _26026) (term301 _26031)). Qed.
Lemma lem1688194 (_26030 : real) (_26031 : real) : (term232 _26030 _26031) = (term232 _26030 _26031).
Proof. exact (eq_refl (term232 _26030 _26031)). Qed.
Lemma lem1688195 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26026 : real) (_26031 : real) : (term326 _26027 _26028 _26030 _26029 _26031 _26026) = (term329 _26027 _26028 _26030 _26029 _26026 _26031).
Proof. exact (MK_COMB (@lem1688194 _26030 _26031) (@lem1688188 _26027 _26028 _26030 _26029 _26026 _26031)). Qed.
Lemma lem1688199 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688200 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term329 _26027 _26028 _26030 _26029 _26026 _26031) = (term330 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (@lem1688199 (term262 _26027 _26028 _26030 _26029 _26031 _26026) (term52 _26030 _26031) (term301 _26031)). Qed.
Lemma lem1688218 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term326 _26027 _26028 _26030 _26029 _26031 _26026) = (term330 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688195 _26027 _26028 _26030 _26029 _26026 _26031) (@lem1688200 _26027 _26028 _26029 _26026 _26030 _26031)). Qed.
Lemma lem1688219 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term303 _26027 _26028 _26030 _26029 _26031 _26026) = (term330 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688171 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1688218 _26027 _26028 _26029 _26026 _26030 _26031)). Qed.
Lemma lem1688220 (_26030 : real) : (term248 _26030) = (term248 _26030).
Proof. exact (eq_refl (term248 _26030)). Qed.
Lemma lem1688221 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term304 _26027 _26028 _26030 _26029 _26031 _26026) = (term331 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688220 _26030) (@lem1688219 _26027 _26028 _26029 _26026 _26030 _26031)). Qed.
Lemma lem1688225 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688226 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term331 _26027 _26028 _26029 _26026 _26030 _26031) = (term332 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (@lem1688225 (term262 _26027 _26028 _26030 _26029 _26031 _26026) (term301 _26030) (term333 _26030 _26031)). Qed.
Lemma lem1688240 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688241 (_26030 : real) (_26031 : real) : (term334 _26030 _26031) = (term335 _26030 _26031).
Proof. exact (@lem1688240 (term52 _26030 _26031) (term301 _26030) (term301 _26031)). Qed.
Lemma lem1688259 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term336 _26027 _26028 _26030 _26029 _26031 _26026) = (term336 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (eq_refl (term336 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688260 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term332 _26027 _26028 _26029 _26026 _26030 _26031) = (term337 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688259 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1688241 _26030 _26031)). Qed.
Lemma lem1688271 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term331 _26027 _26028 _26029 _26026 _26030 _26031) = (term337 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688226 _26027 _26028 _26029 _26026 _26030 _26031) (@lem1688260 _26027 _26028 _26029 _26026 _26030 _26031)). Qed.
Lemma lem1688272 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term304 _26027 _26028 _26030 _26029 _26031 _26026) = (term337 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688221 _26027 _26028 _26029 _26026 _26030 _26031) (@lem1688271 _26027 _26028 _26029 _26026 _26030 _26031)). Qed.
Lemma lem1688273 (_26028 : real) (_26026 : real) : (term253 _26028 _26026) = (term253 _26028 _26026).
Proof. exact (eq_refl (term253 _26028 _26026)). Qed.
Lemma lem1688274 (_26027 : real) (_26028 : real) (_26029 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term305 _26027 _26028 _26030 _26029 _26031 _26026) = (term338 _26027 _26028 _26029 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688273 _26028 _26026) (@lem1688272 _26027 _26028 _26029 _26026 _26030 _26031)). Qed.
Lemma lem1688278 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688279 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term338 _26027 _26028 _26029 _26026 _26030 _26031) = (term339 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688278 (term262 _26027 _26028 _26030 _26029 _26031 _26026) (term296 _26028 _26026) (term335 _26030 _26031)). Qed.
Lemma lem1688293 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688294 (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term340 _26028 _26026 _26030 _26031) = (term341 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688293 (term52 _26030 _26031) (term296 _26028 _26026) (term342 _26030 _26031)). Qed.
Lemma lem1688322 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term336 _26027 _26028 _26030 _26029 _26031 _26026) = (term336 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (eq_refl (term336 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688323 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term339 _26027 _26029 _26028 _26026 _26030 _26031) = (term343 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688322 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1688294 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688334 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term338 _26027 _26028 _26029 _26026 _26030 _26031) = (term343 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688279 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688323 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688335 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term305 _26027 _26028 _26030 _26029 _26031 _26026) = (term343 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688274 _26027 _26028 _26029 _26026 _26030 _26031) (@lem1688334 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688336 (_26027 : real) (_26029 : real) : (term253 _26027 _26029) = (term253 _26027 _26029).
Proof. exact (eq_refl (term253 _26027 _26029)). Qed.
Lemma lem1688337 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term306 _26027 _26028 _26030 _26029 _26031 _26026) = (term344 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688336 _26027 _26029) (@lem1688335 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688341 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688342 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term344 _26027 _26029 _26028 _26026 _26030 _26031) = (term345 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688341 (term262 _26027 _26028 _26030 _26029 _26031 _26026) (term296 _26027 _26029) (term341 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688356 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688357 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term346 _26027 _26029 _26028 _26026 _26030 _26031) = (term347 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688356 (term52 _26030 _26031) (term296 _26027 _26029) (term348 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688395 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term336 _26027 _26028 _26030 _26029 _26031 _26026) = (term336 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (eq_refl (term336 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688396 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term345 _26027 _26029 _26028 _26026 _26030 _26031) = (term349 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688395 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1688357 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688407 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term344 _26027 _26029 _26028 _26026 _26030 _26031) = (term349 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688342 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688396 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688408 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term306 _26027 _26028 _26030 _26029 _26031 _26026) = (term349 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688337 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688407 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1688410 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term350 _26027 _26028 _26030 _26029 _26031 _26026) = (term351 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688409) (@lem1688408 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688454 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1688455 (_26030 : real) (_26031 : real) : (term246 _26030 _26031) = (term333 _26030 _26031).
Proof. exact (@lem1688454 (term52 _26030 _26031) (term301 _26031)). Qed.
Lemma lem1688463 (_26030 : real) : (term248 _26030) = (term248 _26030).
Proof. exact (eq_refl (term248 _26030)). Qed.
Lemma lem1688464 (_26030 : real) (_26031 : real) : (term250 _26030 _26031) = (term334 _26030 _26031).
Proof. exact (MK_COMB (@lem1688463 _26030) (@lem1688455 _26030 _26031)). Qed.
Lemma lem1688468 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688469 (_26030 : real) (_26031 : real) : (term334 _26030 _26031) = (term335 _26030 _26031).
Proof. exact (@lem1688468 (term52 _26030 _26031) (term301 _26030) (term301 _26031)). Qed.
Lemma lem1688487 (_26030 : real) (_26031 : real) : (term250 _26030 _26031) = (term335 _26030 _26031).
Proof. exact (TRANS (@lem1688464 _26030 _26031) (@lem1688469 _26030 _26031)). Qed.
Lemma lem1688488 (_26028 : real) (_26026 : real) : (term253 _26028 _26026) = (term253 _26028 _26026).
Proof. exact (eq_refl (term253 _26028 _26026)). Qed.
Lemma lem1688489 (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term255 _26028 _26026 _26030 _26031) = (term340 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688488 _26028 _26026) (@lem1688487 _26030 _26031)). Qed.
Lemma lem1688493 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688494 (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term340 _26028 _26026 _26030 _26031) = (term341 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688493 (term52 _26030 _26031) (term296 _26028 _26026) (term342 _26030 _26031)). Qed.
Lemma lem1688522 (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term255 _26028 _26026 _26030 _26031) = (term341 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688489 _26028 _26026 _26030 _26031) (@lem1688494 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688523 (_26027 : real) (_26029 : real) : (term253 _26027 _26029) = (term253 _26027 _26029).
Proof. exact (eq_refl (term253 _26027 _26029)). Qed.
Lemma lem1688524 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term259 _26027 _26029 _26028 _26026 _26030 _26031) = (term346 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688523 _26027 _26029) (@lem1688522 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688528 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688529 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term346 _26027 _26029 _26028 _26026 _26030 _26031) = (term347 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688528 (term52 _26030 _26031) (term296 _26027 _26029) (term348 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688567 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term259 _26027 _26029 _26028 _26026 _26030 _26031) = (term347 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688524 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688529 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688568 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term336 _26027 _26028 _26030 _26029 _26031 _26026) = (term336 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (eq_refl (term336 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688569 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term352 _26027 _26029 _26028 _26026 _26030 _26031) = (term349 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688568 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1688567 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688580 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : ((term306 _26027 _26028 _26030 _26029 _26031 _26026) = (term352 _26027 _26029 _26028 _26026 _26030 _26031)) = ((term349 _26027 _26029 _26028 _26026 _26030 _26031) = (term349 _26027 _26029 _26028 _26026 _26030 _26031)).
Proof. exact (MK_COMB (@lem1688410 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688569 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688582 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1688583 (x : Prop) : (x = x) = True.
Proof. exact (@lem1688582 Prop x). Qed.
Lemma lem1688584 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : ((term349 _26027 _26029 _26028 _26026 _26030 _26031) = (term349 _26027 _26029 _26028 _26026 _26030 _26031)) = True.
Proof. exact (@lem1688583 (term349 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688585 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : ((term306 _26027 _26028 _26030 _26029 _26031 _26026) = (term352 _26027 _26029 _26028 _26026 _26030 _26031)) = True.
Proof. exact (TRANS (@lem1688580 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688584 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688586 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : True = ((term306 _26027 _26028 _26030 _26029 _26031 _26026) = (term352 _26027 _26029 _26028 _26026 _26030 _26031)).
Proof. exact (SYM (@lem1688585 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688587 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term306 _26027 _26028 _26030 _26029 _26031 _26026) = (term352 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (EQ_MP (@lem1688586 _26027 _26029 _26028 _26026 _26030 _26031) (@lem0)). Qed.
Lemma lem1688588 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) (h1 : term119) : term352 _26027 _26029 _26028 _26026 _26030 _26031.
Proof. exact (EQ_MP (@lem1688587 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1687878 _26027 _26028 _26030 _26029 _26031 _26026 h1)). Qed.
Lemma lem1688590 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1688591 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term352 _26027 _26029 _26028 _26026 _26030 _26031) = (term353 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (@lem1688590 (term259 _26027 _26029 _26028 _26026 _26030 _26031) (term262 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688593 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1688594 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term354 _26027 _26029 _26028 _26026 _26030 _26031) = (term355 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688593 (term296 _26027 _26029) (term255 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688596 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688597 (_26027 : real) (_26029 : real) : (term356 _26027 _26029) = (real_le _26027 _26029).
Proof. exact (@lem1688596 (real_le _26027 _26029)). Qed.
Lemma lem1688598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1688599 (_26027 : real) (_26029 : real) : (term357 _26027 _26029) = (term358 _26027 _26029).
Proof. exact (MK_COMB (@lem1688598) (@lem1688597 _26027 _26029)). Qed.
Lemma lem1688601 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1688602 (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term359 _26028 _26026 _26030 _26031) = (term360 _26028 _26026 _26030 _26031).
Proof. exact (@lem1688601 (term296 _26028 _26026) (term250 _26030 _26031)). Qed.
Lemma lem1688604 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688605 (_26028 : real) (_26026 : real) : (term356 _26028 _26026) = (real_le _26028 _26026).
Proof. exact (@lem1688604 (real_le _26028 _26026)). Qed.
Lemma lem1688606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1688607 (_26028 : real) (_26026 : real) : (term357 _26028 _26026) = (term358 _26028 _26026).
Proof. exact (MK_COMB (@lem1688606) (@lem1688605 _26028 _26026)). Qed.
Lemma lem1688609 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1688610 (_26030 : real) (_26031 : real) : (term361 _26030 _26031) = (term362 _26030 _26031).
Proof. exact (@lem1688609 (term301 _26030) (term246 _26030 _26031)). Qed.
Lemma lem1688612 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688613 (_26030 : real) : (term363 _26030) = (term247 _26030).
Proof. exact (@lem1688612 (term247 _26030)). Qed.
Lemma lem1688614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1688615 (_26030 : real) : (term364 _26030) = (term365 _26030).
Proof. exact (MK_COMB (@lem1688614) (@lem1688613 _26030)). Qed.
Lemma lem1688617 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1688618 (_26030 : real) (_26031 : real) : (term366 _26030 _26031) = (term367 _26030 _26031).
Proof. exact (@lem1688617 (term301 _26031) (term52 _26030 _26031)). Qed.
Lemma lem1688620 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688621 (_26031 : real) : (term363 _26031) = (term247 _26031).
Proof. exact (@lem1688620 (term247 _26031)). Qed.
Lemma lem1688622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1688623 (_26031 : real) : (term364 _26031) = (term365 _26031).
Proof. exact (MK_COMB (@lem1688622) (@lem1688621 _26031)). Qed.
Lemma lem1688625 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688626 (_26030 : real) (_26031 : real) : (term318 _26030 _26031) = ((real_add _26030 _26031) = term39).
Proof. exact (@lem1688625 ((real_add _26030 _26031) = term39)). Qed.
Lemma lem1688627 (_26030 : real) (_26031 : real) : (term367 _26030 _26031) = (term252 _26030 _26031).
Proof. exact (MK_COMB (@lem1688623 _26031) (@lem1688626 _26030 _26031)). Qed.
Lemma lem1688628 (_26030 : real) (_26031 : real) : (term366 _26030 _26031) = (term252 _26030 _26031).
Proof. exact (TRANS (@lem1688618 _26030 _26031) (@lem1688627 _26030 _26031)). Qed.
Lemma lem1688629 (_26030 : real) (_26031 : real) : (term362 _26030 _26031) = (term257 _26030 _26031).
Proof. exact (MK_COMB (@lem1688615 _26030) (@lem1688628 _26030 _26031)). Qed.
Lemma lem1688630 (_26030 : real) (_26031 : real) : (term361 _26030 _26031) = (term257 _26030 _26031).
Proof. exact (TRANS (@lem1688610 _26030 _26031) (@lem1688629 _26030 _26031)). Qed.
Lemma lem1688631 (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term360 _26028 _26026 _26030 _26031) = (term261 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688607 _26028 _26026) (@lem1688630 _26030 _26031)). Qed.
Lemma lem1688632 (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term359 _26028 _26026 _26030 _26031) = (term261 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688602 _26028 _26026 _26030 _26031) (@lem1688631 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688633 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term355 _26027 _26029 _26028 _26026 _26030 _26031) = (term267 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688599 _26027 _26029) (@lem1688632 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688634 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term354 _26027 _26029 _26028 _26026 _26030 _26031) = (term267 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (TRANS (@lem1688594 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688633 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1688636 (_26027 : real) (_26029 : real) (_26028 : real) (_26026 : real) (_26030 : real) (_26031 : real) : (term368 _26027 _26029 _26028 _26026 _26030 _26031) = (term369 _26027 _26029 _26028 _26026 _26030 _26031).
Proof. exact (MK_COMB (@lem1688635) (@lem1688634 _26027 _26029 _26028 _26026 _26030 _26031)). Qed.
Lemma lem1688637 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term262 _26027 _26028 _26030 _26029 _26031 _26026) = (term262 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (eq_refl (term262 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688638 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term353 _26027 _26028 _26030 _26029 _26031 _26026) = (term137 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (MK_COMB (@lem1688636 _26027 _26029 _26028 _26026 _26030 _26031) (@lem1688637 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688639 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) : (term352 _26027 _26029 _26028 _26026 _26030 _26031) = (term137 _26027 _26028 _26030 _26029 _26031 _26026).
Proof. exact (TRANS (@lem1688591 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1688638 _26027 _26028 _26030 _26029 _26031 _26026)). Qed.
Lemma lem1688641 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term252 u v.
Proof. exact (conj (@lem1688127 a u x v y b h1) (@lem1688134 a u x v y b h1)). Qed.
Lemma lem1688642 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term257 u v.
Proof. exact (conj (@lem1688120 a u x v y b h1) (@lem1688641 a u x v y b h1)). Qed.
Lemma lem1688643 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term261 a y u v.
Proof. exact (conj (@lem1688113 a u x v y b h1) (@lem1688642 a u x v y b h1)). Qed.
Lemma lem1688644 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term370 x a y u v.
Proof. exact (conj (@lem1688106 a u x v y b h1) (@lem1688643 a u x v y b h1)). Qed.
Lemma lem1688646 (_26027 : real) (_26028 : real) (_26030 : real) (_26029 : real) (_26031 : real) (_26026 : real) (h1 : term119) : term137 _26027 _26028 _26030 _26029 _26031 _26026.
Proof. exact (EQ_MP (@lem1688639 _26027 _26028 _26030 _26029 _26031 _26026) (@lem1688588 _26027 _26029 _26028 _26026 _26030 _26031 h1)). Qed.
Lemma lem1688647 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) : term371 a u x v y.
Proof. exact (@lem1688646 a a u x v y h1). Qed.
Lemma lem1688650 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term372 a u x v y.
Proof. exact (@lem1688647 a u x v y h1 (@lem1688644 a u x v y b h2)). Qed.
Lemma lem1688651 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term373 a u x v y.
Proof. exact (fun h0 : term374 a u x v y => @lem1688650 a u x v y b h1 h2). Qed.
Lemma lem1688653 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688654 (a : real) (u : real) (x : real) (v : real) (y : real) : (term373 a u x v y) = (term372 a u x v y).
Proof. exact (@lem1688653 (term372 a u x v y)). Qed.
Lemma lem1688655 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term372 a u x v y.
Proof. exact (EQ_MP (@lem1688654 a u x v y) (@lem1688651 a u x v y b h1 h2)). Qed.
Lemma lem1688673 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688674 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term311 _26043 _26044 _26041 _26042) = (term375 _26043 _26044 _26041 _26042).
Proof. exact (@lem1688673 (real_le _26043 _26044) (term57 _26042 _26044) (term296 _26041 _26042)). Qed.
Lemma lem1688692 (_26041 : real) (_26043 : real) : (term58 _26041 _26043) = (term58 _26041 _26043).
Proof. exact (eq_refl (term58 _26041 _26043)). Qed.
Lemma lem1688693 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term313 _26043 _26044 _26041 _26042) = (term376 _26043 _26044 _26041 _26042).
Proof. exact (MK_COMB (@lem1688692 _26041 _26043) (@lem1688674 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688697 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1688698 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term376 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042).
Proof. exact (@lem1688697 (real_le _26043 _26044) (term57 _26041 _26043) (term378 _26044 _26041 _26042)). Qed.
Lemma lem1688728 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term313 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042).
Proof. exact (TRANS (@lem1688693 _26043 _26044 _26041 _26042) (@lem1688698 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1688730 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term379 _26043 _26044 _26041 _26042) = (term380 _26043 _26044 _26041 _26042).
Proof. exact (MK_COMB (@lem1688729) (@lem1688728 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688760 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term377 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042).
Proof. exact (eq_refl (term377 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688761 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : ((term313 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042)) = ((term377 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042)).
Proof. exact (MK_COMB (@lem1688730 _26043 _26044 _26041 _26042) (@lem1688760 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688763 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1688764 (x : Prop) : (x = x) = True.
Proof. exact (@lem1688763 Prop x). Qed.
Lemma lem1688765 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : ((term377 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042)) = True.
Proof. exact (@lem1688764 (term377 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688766 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : ((term313 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042)) = True.
Proof. exact (TRANS (@lem1688761 _26043 _26044 _26041 _26042) (@lem1688765 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688767 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : True = ((term313 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042)).
Proof. exact (SYM (@lem1688766 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688768 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term313 _26043 _26044 _26041 _26042) = (term377 _26043 _26044 _26041 _26042).
Proof. exact (EQ_MP (@lem1688767 _26043 _26044 _26041 _26042) (@lem0)). Qed.
Lemma lem1688769 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : term377 _26043 _26044 _26041 _26042.
Proof. exact (EQ_MP (@lem1688768 _26043 _26044 _26041 _26042) (@lem1687965 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688771 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1688772 (_26041 : real) (_26042 : real) (_26043 : real) (_26044 : real) : (term377 _26043 _26044 _26041 _26042) = (term381 _26041 _26042 _26043 _26044).
Proof. exact (@lem1688771 (term382 _26043 _26044 _26041 _26042) (real_le _26043 _26044)). Qed.
Lemma lem1688774 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1688775 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term383 _26043 _26044 _26041 _26042) = (term384 _26043 _26044 _26041 _26042).
Proof. exact (@lem1688774 (term57 _26041 _26043) (term378 _26044 _26041 _26042)). Qed.
Lemma lem1688777 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688778 (_26041 : real) (_26043 : real) : (term72 _26041 _26043) = (_26041 = _26043).
Proof. exact (@lem1688777 (_26041 = _26043)). Qed.
Lemma lem1688779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1688780 (_26041 : real) (_26043 : real) : (term73 _26041 _26043) = (term74 _26041 _26043).
Proof. exact (MK_COMB (@lem1688779) (@lem1688778 _26041 _26043)). Qed.
Lemma lem1688782 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1688783 (_26044 : real) (_26041 : real) (_26042 : real) : (term385 _26044 _26041 _26042) = (term386 _26044 _26041 _26042).
Proof. exact (@lem1688782 (term57 _26042 _26044) (term296 _26041 _26042)). Qed.
Lemma lem1688785 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688786 (_26042 : real) (_26044 : real) : (term72 _26042 _26044) = (_26042 = _26044).
Proof. exact (@lem1688785 (_26042 = _26044)). Qed.
Lemma lem1688787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1688788 (_26042 : real) (_26044 : real) : (term73 _26042 _26044) = (term74 _26042 _26044).
Proof. exact (MK_COMB (@lem1688787) (@lem1688786 _26042 _26044)). Qed.
Lemma lem1688790 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688791 (_26041 : real) (_26042 : real) : (term356 _26041 _26042) = (real_le _26041 _26042).
Proof. exact (@lem1688790 (real_le _26041 _26042)). Qed.
Lemma lem1688792 (_26044 : real) (_26041 : real) (_26042 : real) : (term386 _26044 _26041 _26042) = (term387 _26044 _26041 _26042).
Proof. exact (MK_COMB (@lem1688788 _26042 _26044) (@lem1688791 _26041 _26042)). Qed.
Lemma lem1688793 (_26044 : real) (_26041 : real) (_26042 : real) : (term385 _26044 _26041 _26042) = (term387 _26044 _26041 _26042).
Proof. exact (TRANS (@lem1688783 _26044 _26041 _26042) (@lem1688792 _26044 _26041 _26042)). Qed.
Lemma lem1688794 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term384 _26043 _26044 _26041 _26042) = (term388 _26043 _26044 _26041 _26042).
Proof. exact (MK_COMB (@lem1688780 _26041 _26043) (@lem1688793 _26044 _26041 _26042)). Qed.
Lemma lem1688795 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term383 _26043 _26044 _26041 _26042) = (term388 _26043 _26044 _26041 _26042).
Proof. exact (TRANS (@lem1688775 _26043 _26044 _26041 _26042) (@lem1688794 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688796 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1688797 (_26043 : real) (_26044 : real) (_26041 : real) (_26042 : real) : (term389 _26043 _26044 _26041 _26042) = (term390 _26043 _26044 _26041 _26042).
Proof. exact (MK_COMB (@lem1688796) (@lem1688795 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688798 (_26043 : real) (_26044 : real) : (real_le _26043 _26044) = (real_le _26043 _26044).
Proof. exact (eq_refl (real_le _26043 _26044)). Qed.
Lemma lem1688799 (_26041 : real) (_26042 : real) (_26043 : real) (_26044 : real) : (term381 _26041 _26042 _26043 _26044) = (term391 _26041 _26042 _26043 _26044).
Proof. exact (MK_COMB (@lem1688797 _26043 _26044 _26041 _26042) (@lem1688798 _26043 _26044)). Qed.
Lemma lem1688800 (_26041 : real) (_26042 : real) (_26043 : real) (_26044 : real) : (term377 _26043 _26044 _26041 _26042) = (term391 _26041 _26042 _26043 _26044).
Proof. exact (TRANS (@lem1688772 _26041 _26042 _26043 _26044) (@lem1688799 _26041 _26042 _26043 _26044)). Qed.
Lemma lem1688802 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term392 a u x v y.
Proof. exact (conj (@lem1688099 u x v y) (@lem1688655 a u x v y b h1 h2)). Qed.
Lemma lem1688803 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term393 a u x v y.
Proof. exact (conj (@lem1688091 a u x v y b h2 h3) (@lem1688802 a u x v y b h1 h3)). Qed.
Lemma lem1688805 (_26041 : real) (_26042 : real) (_26043 : real) (_26044 : real) : term391 _26041 _26042 _26043 _26044.
Proof. exact (EQ_MP (@lem1688800 _26041 _26042 _26043 _26044) (@lem1688769 _26043 _26044 _26041 _26042)). Qed.
Lemma lem1688806 (a : real) (u : real) (x : real) (v : real) (y : real) : term394 a u x v y.
Proof. exact (@lem1688805 (term31 u v a) (term321 u x v y) a (term321 u x v y)). Qed.
Lemma lem1688809 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term166 a u x v y.
Proof. exact (@lem1688806 a u x v y (@lem1688803 a u x v y b h1 h2 h3)). Qed.
Lemma lem1688810 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term395 a u x v y.
Proof. exact (fun h0 : term284 a u x v y => @lem1688809 a u x v y b h1 h2 h3). Qed.
Lemma lem1688812 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688813 (a : real) (u : real) (x : real) (v : real) (y : real) : (term395 a u x v y) = (term166 a u x v y).
Proof. exact (@lem1688812 (term166 a u x v y)). Qed.
Lemma lem1688814 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term166 a u x v y.
Proof. exact (EQ_MP (@lem1688813 a u x v y) (@lem1688810 a u x v y b h1 h2 h3)). Qed.
Lemma lem1688817 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1688819 (a : real) (u : real) (x : real) (v : real) (y : real) : (term284 a u x v y) = (term396 a u x v y).
Proof. exact (@lem1688817 (term166 a u x v y)). Qed.
Lemma lem1688822 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term284 a u x v y) : term396 a u x v y.
Proof. exact (EQ_MP (@lem1688819 a u x v y) (@lem1687894 a u x v y h1)). Qed.
Lemma lem1688825 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (@lem1688822 a u x v y h3 (@lem1688814 a u x v y b h1 h2 h4)). Qed.
Lemma lem1688826 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : term109.
Proof. exact (fun h0 : ~ False => @lem1688825 a u x v y b h1 h2 h3 h4). Qed.
Lemma lem1688828 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688829 : term109 = False.
Proof. exact (@lem1688828 False). Qed.
Lemma lem1688830 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1688829) (@lem1688826 a u x v y b h1 h2 h3 h4)). Qed.
Lemma lem1688831 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1688832 (_26059 : real) (_26061 : real) (h1 : _26059 = _26061) : _26059 = _26061.
Proof. exact (h1). Qed.
Lemma lem1688833 (_26060 : real) (_26062 : real) (h1 : _26060 = _26062) : _26060 = _26062.
Proof. exact (h1). Qed.
Lemma lem1688834 (_26059 : real) (_26061 : real) (h1 : _26059 = _26061) : (real_le _26059) = (real_le _26061).
Proof. exact (MK_COMB (@lem1688831) (@lem1688832 _26059 _26061 h1)). Qed.
Lemma lem1688835 (_26059 : real) (_26061 : real) (_26060 : real) (_26062 : real) (h1 : _26059 = _26061) (h2 : _26060 = _26062) : (real_le _26059 _26060) = (real_le _26061 _26062).
Proof. exact (MK_COMB (@lem1688834 _26059 _26061 h1) (@lem1688833 _26060 _26062 h2)). Qed.
Lemma lem1688837 (b : Prop) (a : Prop) : term307 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1688838 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : term308 _26061 _26062 _26059 _26060.
Proof. exact (@lem1688837 (real_le _26061 _26062) (real_le _26059 _26060)). Qed.
Lemma lem1688839 (_26059 : real) (_26061 : real) (_26060 : real) (_26062 : real) (h1 : _26059 = _26061) (h2 : _26060 = _26062) : term309 _26061 _26062 _26059 _26060.
Proof. exact (@lem1688838 _26061 _26062 _26059 _26060 (@lem1688835 _26059 _26061 _26060 _26062 h1 h2)). Qed.
Lemma lem1688840 (_26062 : real) (_26060 : real) (_26059 : real) (_26061 : real) (h1 : _26059 = _26061) : term310 _26061 _26062 _26059 _26060.
Proof. exact (fun h0 : _26060 = _26062 => @lem1688839 _26059 _26061 _26060 _26062 h1 h0). Qed.
Lemma lem1688842 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1688843 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term310 _26061 _26062 _26059 _26060) = (term311 _26061 _26062 _26059 _26060).
Proof. exact (@lem1688842 (_26060 = _26062) (term309 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1688844 (_26062 : real) (_26060 : real) (_26059 : real) (_26061 : real) (h1 : _26059 = _26061) : term311 _26061 _26062 _26059 _26060.
Proof. exact (EQ_MP (@lem1688843 _26061 _26062 _26059 _26060) (@lem1688840 _26062 _26060 _26059 _26061 h1)). Qed.
Lemma lem1688845 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : term312 _26061 _26062 _26059 _26060.
Proof. exact (fun h0 : _26059 = _26061 => @lem1688844 _26062 _26060 _26059 _26061 h0). Qed.
Lemma lem1688847 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1688848 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term312 _26061 _26062 _26059 _26060) = (term313 _26061 _26062 _26059 _26060).
Proof. exact (@lem1688847 (_26059 = _26061) (term311 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1688849 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : term313 _26061 _26062 _26059 _26060.
Proof. exact (EQ_MP (@lem1688848 _26061 _26062 _26059 _26060) (@lem1688845 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1688909 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1688910 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (@lem1688909 (term321 u x v y)). Qed.
Lemma lem1688911 (u : real) (x : real) (v : real) (y : real) : term322 u x v y.
Proof. exact (fun h0 : term323 u x v y => @lem1688910 u x v y). Qed.
Lemma lem1688913 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688914 (u : real) (x : real) (v : real) (y : real) : (term322 u x v y) = ((term321 u x v y) = (term321 u x v y)).
Proof. exact (@lem1688913 ((term321 u x v y) = (term321 u x v y))). Qed.
Lemma lem1688915 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (EQ_MP (@lem1688914 u x v y) (@lem1688911 u x v y)). Qed.
Lemma lem1688917 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1687527 a u x v y b h1)). Qed.
Lemma lem1688918 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1688917 a u x v y b h1). Qed.
Lemma lem1688920 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688921 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1688920 ((real_add u v) = term39)). Qed.
Lemma lem1688922 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1688921 u v) (@lem1688918 a u x v y b h1)). Qed.
Lemma lem1688928 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1688929 (_26034 : real) (_26032 : real) (_26033 : real) : (term217 _26032 _26033 _26034) = (term314 _26034 _26032 _26033).
Proof. exact (@lem1688928 ((term31 _26032 _26033 _26034) = _26034) (term52 _26032 _26033)). Qed.
Lemma lem1688939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1688940 (_26034 : real) (_26032 : real) (_26033 : real) : (term315 _26032 _26033 _26034) = (term316 _26034 _26032 _26033).
Proof. exact (MK_COMB (@lem1688939) (@lem1688929 _26034 _26032 _26033)). Qed.
Lemma lem1688950 (_26034 : real) (_26032 : real) (_26033 : real) : (term314 _26034 _26032 _26033) = (term314 _26034 _26032 _26033).
Proof. exact (eq_refl (term314 _26034 _26032 _26033)). Qed.
Lemma lem1688951 (_26034 : real) (_26032 : real) (_26033 : real) : ((term217 _26032 _26033 _26034) = (term314 _26034 _26032 _26033)) = ((term314 _26034 _26032 _26033) = (term314 _26034 _26032 _26033)).
Proof. exact (MK_COMB (@lem1688940 _26034 _26032 _26033) (@lem1688950 _26034 _26032 _26033)). Qed.
Lemma lem1688953 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1688954 (x : Prop) : (x = x) = True.
Proof. exact (@lem1688953 Prop x). Qed.
Lemma lem1688955 (_26034 : real) (_26032 : real) (_26033 : real) : ((term314 _26034 _26032 _26033) = (term314 _26034 _26032 _26033)) = True.
Proof. exact (@lem1688954 (term314 _26034 _26032 _26033)). Qed.
Lemma lem1688956 (_26034 : real) (_26032 : real) (_26033 : real) : ((term217 _26032 _26033 _26034) = (term314 _26034 _26032 _26033)) = True.
Proof. exact (TRANS (@lem1688951 _26034 _26032 _26033) (@lem1688955 _26034 _26032 _26033)). Qed.
Lemma lem1688957 (_26034 : real) (_26032 : real) (_26033 : real) : True = ((term217 _26032 _26033 _26034) = (term314 _26034 _26032 _26033)).
Proof. exact (SYM (@lem1688956 _26034 _26032 _26033)). Qed.
Lemma lem1688958 (_26034 : real) (_26032 : real) (_26033 : real) : (term217 _26032 _26033 _26034) = (term314 _26034 _26032 _26033).
Proof. exact (EQ_MP (@lem1688957 _26034 _26032 _26033) (@lem0)). Qed.
Lemma lem1688959 (_26034 : real) (_26032 : real) (_26033 : real) (h1 : term122) : term314 _26034 _26032 _26033.
Proof. exact (EQ_MP (@lem1688958 _26034 _26032 _26033) (@lem1687900 _26032 _26033 _26034 h1)). Qed.
Lemma lem1688961 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1688962 (_26032 : real) (_26033 : real) (_26034 : real) : (term314 _26034 _26032 _26033) = (term317 _26032 _26033 _26034).
Proof. exact (@lem1688961 (term52 _26032 _26033) ((term31 _26032 _26033 _26034) = _26034)). Qed.
Lemma lem1688964 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1688965 (_26032 : real) (_26033 : real) : (term318 _26032 _26033) = ((real_add _26032 _26033) = term39).
Proof. exact (@lem1688964 ((real_add _26032 _26033) = term39)). Qed.
Lemma lem1688966 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1688967 (_26032 : real) (_26033 : real) : (term319 _26032 _26033) = (term320 _26032 _26033).
Proof. exact (MK_COMB (@lem1688966) (@lem1688965 _26032 _26033)). Qed.
Lemma lem1688968 (_26032 : real) (_26033 : real) (_26034 : real) : ((term31 _26032 _26033 _26034) = _26034) = ((term31 _26032 _26033 _26034) = _26034).
Proof. exact (eq_refl ((term31 _26032 _26033 _26034) = _26034)). Qed.
Lemma lem1688969 (_26032 : real) (_26033 : real) (_26034 : real) : (term317 _26032 _26033 _26034) = (term1 _26032 _26033 _26034).
Proof. exact (MK_COMB (@lem1688967 _26032 _26033) (@lem1688968 _26032 _26033 _26034)). Qed.
Lemma lem1688970 (_26032 : real) (_26033 : real) (_26034 : real) : (term314 _26034 _26032 _26033) = (term1 _26032 _26033 _26034).
Proof. exact (TRANS (@lem1688962 _26032 _26033 _26034) (@lem1688969 _26032 _26033 _26034)). Qed.
Lemma lem1688973 (_26032 : real) (_26033 : real) (_26034 : real) (h1 : term122) : term1 _26032 _26033 _26034.
Proof. exact (EQ_MP (@lem1688970 _26032 _26033 _26034) (@lem1688959 _26034 _26032 _26033 h1)). Qed.
Lemma lem1688974 (u : real) (v : real) (_26034 : real) (h1 : term122) : term1 u v _26034.
Proof. exact (@lem1688973 u v _26034 h1). Qed.
Lemma lem1688977 (_26034 : real) (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v _26034) = _26034.
Proof. exact (@lem1688974 u v _26034 h1 (@lem1688922 a u x v y b h2)). Qed.
Lemma lem1688978 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v b) = b.
Proof. exact (@lem1688977 b a u x v y b h1 h2). Qed.
Lemma lem1688979 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : term107 u v b.
Proof. exact (fun h0 : term44 u v b => @lem1688978 a u x v y b h1 h2). Qed.
Lemma lem1688981 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688982 (u : real) (v : real) (b : real) : (term107 u v b) = ((term31 u v b) = b).
Proof. exact (@lem1688981 ((term31 u v b) = b)). Qed.
Lemma lem1688983 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v b) = b.
Proof. exact (EQ_MP (@lem1688982 u v b) (@lem1688979 a u x v y b h1 h2)). Qed.
Lemma lem1688985 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le x b.
Proof. exact (proj1 (@lem1687519 a u x v y b h1)). Qed.
Lemma lem1688986 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 x b.
Proof. exact (fun h0 : term296 x b => @lem1688985 a u x v y b h1). Qed.
Lemma lem1688988 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688989 (x : real) (b : real) : (term324 x b) = (real_le x b).
Proof. exact (@lem1688988 (real_le x b)). Qed.
Lemma lem1688990 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le x b.
Proof. exact (EQ_MP (@lem1688989 x b) (@lem1688986 a u x v y b h1)). Qed.
Lemma lem1688992 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le y b.
Proof. exact (proj1 (@lem1687523 a u x v y b h1)). Qed.
Lemma lem1688993 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 y b.
Proof. exact (fun h0 : term296 y b => @lem1688992 a u x v y b h1). Qed.
Lemma lem1688995 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1688996 (y : real) (b : real) : (term324 y b) = (real_le y b).
Proof. exact (@lem1688995 (real_le y b)). Qed.
Lemma lem1688997 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_le y b.
Proof. exact (EQ_MP (@lem1688996 y b) (@lem1688993 a u x v y b h1)). Qed.
Lemma lem1688999 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (proj1 (@lem1687525 a u x v y b h1)). Qed.
Lemma lem1689000 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 u.
Proof. exact (fun h0 : term301 u => @lem1688999 a u x v y b h1). Qed.
Lemma lem1689002 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1689003 (u : real) : (term325 u) = (term247 u).
Proof. exact (@lem1689002 (term247 u)). Qed.
Lemma lem1689004 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (EQ_MP (@lem1689003 u) (@lem1689000 a u x v y b h1)). Qed.
Lemma lem1689006 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (proj1 (@lem1687527 a u x v y b h1)). Qed.
Lemma lem1689007 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 v.
Proof. exact (fun h0 : term301 v => @lem1689006 a u x v y b h1). Qed.
Lemma lem1689009 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1689010 (v : real) : (term325 v) = (term247 v).
Proof. exact (@lem1689009 (term247 v)). Qed.
Lemma lem1689011 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (EQ_MP (@lem1689010 v) (@lem1689007 a u x v y b h1)). Qed.
Lemma lem1689013 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1687527 a u x v y b h1)). Qed.
Lemma lem1689014 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1689013 a u x v y b h1). Qed.
Lemma lem1689016 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1689017 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1689016 ((real_add u v) = term39)). Qed.
Lemma lem1689018 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1689017 u v) (@lem1689014 a u x v y b h1)). Qed.
Lemma lem1689054 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689055 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term303 _26036 _26037 _26039 _26038 _26040 _26035) = (term326 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (@lem1689054 (term52 _26039 _26040) (term301 _26040) (term262 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689071 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1689072 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26035 : real) (_26040 : real) : (term327 _26036 _26037 _26039 _26038 _26040 _26035) = (term328 _26036 _26037 _26039 _26038 _26035 _26040).
Proof. exact (@lem1689071 (term262 _26036 _26037 _26039 _26038 _26040 _26035) (term301 _26040)). Qed.
Lemma lem1689078 (_26039 : real) (_26040 : real) : (term232 _26039 _26040) = (term232 _26039 _26040).
Proof. exact (eq_refl (term232 _26039 _26040)). Qed.
Lemma lem1689079 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26035 : real) (_26040 : real) : (term326 _26036 _26037 _26039 _26038 _26040 _26035) = (term329 _26036 _26037 _26039 _26038 _26035 _26040).
Proof. exact (MK_COMB (@lem1689078 _26039 _26040) (@lem1689072 _26036 _26037 _26039 _26038 _26035 _26040)). Qed.
Lemma lem1689083 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689084 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term329 _26036 _26037 _26039 _26038 _26035 _26040) = (term330 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (@lem1689083 (term262 _26036 _26037 _26039 _26038 _26040 _26035) (term52 _26039 _26040) (term301 _26040)). Qed.
Lemma lem1689102 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term326 _26036 _26037 _26039 _26038 _26040 _26035) = (term330 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689079 _26036 _26037 _26039 _26038 _26035 _26040) (@lem1689084 _26036 _26037 _26038 _26035 _26039 _26040)). Qed.
Lemma lem1689103 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term303 _26036 _26037 _26039 _26038 _26040 _26035) = (term330 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689055 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1689102 _26036 _26037 _26038 _26035 _26039 _26040)). Qed.
Lemma lem1689104 (_26039 : real) : (term248 _26039) = (term248 _26039).
Proof. exact (eq_refl (term248 _26039)). Qed.
Lemma lem1689105 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term304 _26036 _26037 _26039 _26038 _26040 _26035) = (term331 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689104 _26039) (@lem1689103 _26036 _26037 _26038 _26035 _26039 _26040)). Qed.
Lemma lem1689109 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689110 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term331 _26036 _26037 _26038 _26035 _26039 _26040) = (term332 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (@lem1689109 (term262 _26036 _26037 _26039 _26038 _26040 _26035) (term301 _26039) (term333 _26039 _26040)). Qed.
Lemma lem1689124 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689125 (_26039 : real) (_26040 : real) : (term334 _26039 _26040) = (term335 _26039 _26040).
Proof. exact (@lem1689124 (term52 _26039 _26040) (term301 _26039) (term301 _26040)). Qed.
Lemma lem1689143 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term336 _26036 _26037 _26039 _26038 _26040 _26035) = (term336 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (eq_refl (term336 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689144 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term332 _26036 _26037 _26038 _26035 _26039 _26040) = (term337 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689143 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1689125 _26039 _26040)). Qed.
Lemma lem1689155 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term331 _26036 _26037 _26038 _26035 _26039 _26040) = (term337 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689110 _26036 _26037 _26038 _26035 _26039 _26040) (@lem1689144 _26036 _26037 _26038 _26035 _26039 _26040)). Qed.
Lemma lem1689156 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term304 _26036 _26037 _26039 _26038 _26040 _26035) = (term337 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689105 _26036 _26037 _26038 _26035 _26039 _26040) (@lem1689155 _26036 _26037 _26038 _26035 _26039 _26040)). Qed.
Lemma lem1689157 (_26037 : real) (_26035 : real) : (term253 _26037 _26035) = (term253 _26037 _26035).
Proof. exact (eq_refl (term253 _26037 _26035)). Qed.
Lemma lem1689158 (_26036 : real) (_26037 : real) (_26038 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term305 _26036 _26037 _26039 _26038 _26040 _26035) = (term338 _26036 _26037 _26038 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689157 _26037 _26035) (@lem1689156 _26036 _26037 _26038 _26035 _26039 _26040)). Qed.
Lemma lem1689162 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689163 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term338 _26036 _26037 _26038 _26035 _26039 _26040) = (term339 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689162 (term262 _26036 _26037 _26039 _26038 _26040 _26035) (term296 _26037 _26035) (term335 _26039 _26040)). Qed.
Lemma lem1689177 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689178 (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term340 _26037 _26035 _26039 _26040) = (term341 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689177 (term52 _26039 _26040) (term296 _26037 _26035) (term342 _26039 _26040)). Qed.
Lemma lem1689206 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term336 _26036 _26037 _26039 _26038 _26040 _26035) = (term336 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (eq_refl (term336 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689207 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term339 _26036 _26038 _26037 _26035 _26039 _26040) = (term343 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689206 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1689178 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689218 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term338 _26036 _26037 _26038 _26035 _26039 _26040) = (term343 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689163 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689207 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689219 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term305 _26036 _26037 _26039 _26038 _26040 _26035) = (term343 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689158 _26036 _26037 _26038 _26035 _26039 _26040) (@lem1689218 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689220 (_26036 : real) (_26038 : real) : (term253 _26036 _26038) = (term253 _26036 _26038).
Proof. exact (eq_refl (term253 _26036 _26038)). Qed.
Lemma lem1689221 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term306 _26036 _26037 _26039 _26038 _26040 _26035) = (term344 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689220 _26036 _26038) (@lem1689219 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689225 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689226 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term344 _26036 _26038 _26037 _26035 _26039 _26040) = (term345 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689225 (term262 _26036 _26037 _26039 _26038 _26040 _26035) (term296 _26036 _26038) (term341 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689240 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689241 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term346 _26036 _26038 _26037 _26035 _26039 _26040) = (term347 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689240 (term52 _26039 _26040) (term296 _26036 _26038) (term348 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689279 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term336 _26036 _26037 _26039 _26038 _26040 _26035) = (term336 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (eq_refl (term336 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689280 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term345 _26036 _26038 _26037 _26035 _26039 _26040) = (term349 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689279 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1689241 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689291 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term344 _26036 _26038 _26037 _26035 _26039 _26040) = (term349 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689226 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689280 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689292 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term306 _26036 _26037 _26039 _26038 _26040 _26035) = (term349 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689221 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689291 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1689294 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term350 _26036 _26037 _26039 _26038 _26040 _26035) = (term351 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689293) (@lem1689292 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689338 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1689339 (_26039 : real) (_26040 : real) : (term246 _26039 _26040) = (term333 _26039 _26040).
Proof. exact (@lem1689338 (term52 _26039 _26040) (term301 _26040)). Qed.
Lemma lem1689347 (_26039 : real) : (term248 _26039) = (term248 _26039).
Proof. exact (eq_refl (term248 _26039)). Qed.
Lemma lem1689348 (_26039 : real) (_26040 : real) : (term250 _26039 _26040) = (term334 _26039 _26040).
Proof. exact (MK_COMB (@lem1689347 _26039) (@lem1689339 _26039 _26040)). Qed.
Lemma lem1689352 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689353 (_26039 : real) (_26040 : real) : (term334 _26039 _26040) = (term335 _26039 _26040).
Proof. exact (@lem1689352 (term52 _26039 _26040) (term301 _26039) (term301 _26040)). Qed.
Lemma lem1689371 (_26039 : real) (_26040 : real) : (term250 _26039 _26040) = (term335 _26039 _26040).
Proof. exact (TRANS (@lem1689348 _26039 _26040) (@lem1689353 _26039 _26040)). Qed.
Lemma lem1689372 (_26037 : real) (_26035 : real) : (term253 _26037 _26035) = (term253 _26037 _26035).
Proof. exact (eq_refl (term253 _26037 _26035)). Qed.
Lemma lem1689373 (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term255 _26037 _26035 _26039 _26040) = (term340 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689372 _26037 _26035) (@lem1689371 _26039 _26040)). Qed.
Lemma lem1689377 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689378 (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term340 _26037 _26035 _26039 _26040) = (term341 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689377 (term52 _26039 _26040) (term296 _26037 _26035) (term342 _26039 _26040)). Qed.
Lemma lem1689406 (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term255 _26037 _26035 _26039 _26040) = (term341 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689373 _26037 _26035 _26039 _26040) (@lem1689378 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689407 (_26036 : real) (_26038 : real) : (term253 _26036 _26038) = (term253 _26036 _26038).
Proof. exact (eq_refl (term253 _26036 _26038)). Qed.
Lemma lem1689408 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term259 _26036 _26038 _26037 _26035 _26039 _26040) = (term346 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689407 _26036 _26038) (@lem1689406 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689412 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689413 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term346 _26036 _26038 _26037 _26035 _26039 _26040) = (term347 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689412 (term52 _26039 _26040) (term296 _26036 _26038) (term348 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689451 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term259 _26036 _26038 _26037 _26035 _26039 _26040) = (term347 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689408 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689413 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689452 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term336 _26036 _26037 _26039 _26038 _26040 _26035) = (term336 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (eq_refl (term336 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689453 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term352 _26036 _26038 _26037 _26035 _26039 _26040) = (term349 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689452 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1689451 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689464 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : ((term306 _26036 _26037 _26039 _26038 _26040 _26035) = (term352 _26036 _26038 _26037 _26035 _26039 _26040)) = ((term349 _26036 _26038 _26037 _26035 _26039 _26040) = (term349 _26036 _26038 _26037 _26035 _26039 _26040)).
Proof. exact (MK_COMB (@lem1689294 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689453 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689466 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1689467 (x : Prop) : (x = x) = True.
Proof. exact (@lem1689466 Prop x). Qed.
Lemma lem1689468 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : ((term349 _26036 _26038 _26037 _26035 _26039 _26040) = (term349 _26036 _26038 _26037 _26035 _26039 _26040)) = True.
Proof. exact (@lem1689467 (term349 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689469 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : ((term306 _26036 _26037 _26039 _26038 _26040 _26035) = (term352 _26036 _26038 _26037 _26035 _26039 _26040)) = True.
Proof. exact (TRANS (@lem1689464 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689468 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689470 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : True = ((term306 _26036 _26037 _26039 _26038 _26040 _26035) = (term352 _26036 _26038 _26037 _26035 _26039 _26040)).
Proof. exact (SYM (@lem1689469 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689471 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term306 _26036 _26037 _26039 _26038 _26040 _26035) = (term352 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (EQ_MP (@lem1689470 _26036 _26038 _26037 _26035 _26039 _26040) (@lem0)). Qed.
Lemma lem1689472 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) (h1 : term119) : term352 _26036 _26038 _26037 _26035 _26039 _26040.
Proof. exact (EQ_MP (@lem1689471 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1687930 _26036 _26037 _26039 _26038 _26040 _26035 h1)). Qed.
Lemma lem1689474 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1689475 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term352 _26036 _26038 _26037 _26035 _26039 _26040) = (term353 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (@lem1689474 (term259 _26036 _26038 _26037 _26035 _26039 _26040) (term262 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689477 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1689478 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term354 _26036 _26038 _26037 _26035 _26039 _26040) = (term355 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689477 (term296 _26036 _26038) (term255 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689480 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689481 (_26036 : real) (_26038 : real) : (term356 _26036 _26038) = (real_le _26036 _26038).
Proof. exact (@lem1689480 (real_le _26036 _26038)). Qed.
Lemma lem1689482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1689483 (_26036 : real) (_26038 : real) : (term357 _26036 _26038) = (term358 _26036 _26038).
Proof. exact (MK_COMB (@lem1689482) (@lem1689481 _26036 _26038)). Qed.
Lemma lem1689485 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1689486 (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term359 _26037 _26035 _26039 _26040) = (term360 _26037 _26035 _26039 _26040).
Proof. exact (@lem1689485 (term296 _26037 _26035) (term250 _26039 _26040)). Qed.
Lemma lem1689488 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689489 (_26037 : real) (_26035 : real) : (term356 _26037 _26035) = (real_le _26037 _26035).
Proof. exact (@lem1689488 (real_le _26037 _26035)). Qed.
Lemma lem1689490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1689491 (_26037 : real) (_26035 : real) : (term357 _26037 _26035) = (term358 _26037 _26035).
Proof. exact (MK_COMB (@lem1689490) (@lem1689489 _26037 _26035)). Qed.
Lemma lem1689493 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1689494 (_26039 : real) (_26040 : real) : (term361 _26039 _26040) = (term362 _26039 _26040).
Proof. exact (@lem1689493 (term301 _26039) (term246 _26039 _26040)). Qed.
Lemma lem1689496 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689497 (_26039 : real) : (term363 _26039) = (term247 _26039).
Proof. exact (@lem1689496 (term247 _26039)). Qed.
Lemma lem1689498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1689499 (_26039 : real) : (term364 _26039) = (term365 _26039).
Proof. exact (MK_COMB (@lem1689498) (@lem1689497 _26039)). Qed.
Lemma lem1689501 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1689502 (_26039 : real) (_26040 : real) : (term366 _26039 _26040) = (term367 _26039 _26040).
Proof. exact (@lem1689501 (term301 _26040) (term52 _26039 _26040)). Qed.
Lemma lem1689504 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689505 (_26040 : real) : (term363 _26040) = (term247 _26040).
Proof. exact (@lem1689504 (term247 _26040)). Qed.
Lemma lem1689506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1689507 (_26040 : real) : (term364 _26040) = (term365 _26040).
Proof. exact (MK_COMB (@lem1689506) (@lem1689505 _26040)). Qed.
Lemma lem1689509 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689510 (_26039 : real) (_26040 : real) : (term318 _26039 _26040) = ((real_add _26039 _26040) = term39).
Proof. exact (@lem1689509 ((real_add _26039 _26040) = term39)). Qed.
Lemma lem1689511 (_26039 : real) (_26040 : real) : (term367 _26039 _26040) = (term252 _26039 _26040).
Proof. exact (MK_COMB (@lem1689507 _26040) (@lem1689510 _26039 _26040)). Qed.
Lemma lem1689512 (_26039 : real) (_26040 : real) : (term366 _26039 _26040) = (term252 _26039 _26040).
Proof. exact (TRANS (@lem1689502 _26039 _26040) (@lem1689511 _26039 _26040)). Qed.
Lemma lem1689513 (_26039 : real) (_26040 : real) : (term362 _26039 _26040) = (term257 _26039 _26040).
Proof. exact (MK_COMB (@lem1689499 _26039) (@lem1689512 _26039 _26040)). Qed.
Lemma lem1689514 (_26039 : real) (_26040 : real) : (term361 _26039 _26040) = (term257 _26039 _26040).
Proof. exact (TRANS (@lem1689494 _26039 _26040) (@lem1689513 _26039 _26040)). Qed.
Lemma lem1689515 (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term360 _26037 _26035 _26039 _26040) = (term261 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689491 _26037 _26035) (@lem1689514 _26039 _26040)). Qed.
Lemma lem1689516 (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term359 _26037 _26035 _26039 _26040) = (term261 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689486 _26037 _26035 _26039 _26040) (@lem1689515 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689517 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term355 _26036 _26038 _26037 _26035 _26039 _26040) = (term267 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689483 _26036 _26038) (@lem1689516 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689518 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term354 _26036 _26038 _26037 _26035 _26039 _26040) = (term267 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (TRANS (@lem1689478 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689517 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689519 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1689520 (_26036 : real) (_26038 : real) (_26037 : real) (_26035 : real) (_26039 : real) (_26040 : real) : (term368 _26036 _26038 _26037 _26035 _26039 _26040) = (term369 _26036 _26038 _26037 _26035 _26039 _26040).
Proof. exact (MK_COMB (@lem1689519) (@lem1689518 _26036 _26038 _26037 _26035 _26039 _26040)). Qed.
Lemma lem1689521 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term262 _26036 _26037 _26039 _26038 _26040 _26035) = (term262 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (eq_refl (term262 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689522 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term353 _26036 _26037 _26039 _26038 _26040 _26035) = (term137 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (MK_COMB (@lem1689520 _26036 _26038 _26037 _26035 _26039 _26040) (@lem1689521 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689523 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) : (term352 _26036 _26038 _26037 _26035 _26039 _26040) = (term137 _26036 _26037 _26039 _26038 _26040 _26035).
Proof. exact (TRANS (@lem1689475 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1689522 _26036 _26037 _26039 _26038 _26040 _26035)). Qed.
Lemma lem1689525 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term252 u v.
Proof. exact (conj (@lem1689011 a u x v y b h1) (@lem1689018 a u x v y b h1)). Qed.
Lemma lem1689526 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term257 u v.
Proof. exact (conj (@lem1689004 a u x v y b h1) (@lem1689525 a u x v y b h1)). Qed.
Lemma lem1689527 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term261 y b u v.
Proof. exact (conj (@lem1688997 a u x v y b h1) (@lem1689526 a u x v y b h1)). Qed.
Lemma lem1689528 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term397 x y b u v.
Proof. exact (conj (@lem1688990 a u x v y b h1) (@lem1689527 a u x v y b h1)). Qed.
Lemma lem1689530 (_26036 : real) (_26037 : real) (_26039 : real) (_26038 : real) (_26040 : real) (_26035 : real) (h1 : term119) : term137 _26036 _26037 _26039 _26038 _26040 _26035.
Proof. exact (EQ_MP (@lem1689523 _26036 _26037 _26039 _26038 _26040 _26035) (@lem1689472 _26036 _26038 _26037 _26035 _26039 _26040 h1)). Qed.
Lemma lem1689531 (x : real) (y : real) (u : real) (v : real) (b : real) (h1 : term119) : term398 x y u v b.
Proof. exact (@lem1689530 x y u b v b h1). Qed.
Lemma lem1689534 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term399 x y u v b.
Proof. exact (@lem1689531 x y u v b h1 (@lem1689528 a u x v y b h2)). Qed.
Lemma lem1689535 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term400 x y u v b.
Proof. exact (fun h0 : term401 x y u v b => @lem1689534 a u x v y b h1 h2). Qed.
Lemma lem1689537 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1689538 (x : real) (y : real) (u : real) (v : real) (b : real) : (term400 x y u v b) = (term399 x y u v b).
Proof. exact (@lem1689537 (term399 x y u v b)). Qed.
Lemma lem1689539 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term399 x y u v b.
Proof. exact (EQ_MP (@lem1689538 x y u v b) (@lem1689535 a u x v y b h1 h2)). Qed.
Lemma lem1689557 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689558 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term311 _26061 _26062 _26059 _26060) = (term375 _26061 _26062 _26059 _26060).
Proof. exact (@lem1689557 (real_le _26061 _26062) (term57 _26060 _26062) (term296 _26059 _26060)). Qed.
Lemma lem1689576 (_26059 : real) (_26061 : real) : (term58 _26059 _26061) = (term58 _26059 _26061).
Proof. exact (eq_refl (term58 _26059 _26061)). Qed.
Lemma lem1689577 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term313 _26061 _26062 _26059 _26060) = (term376 _26061 _26062 _26059 _26060).
Proof. exact (MK_COMB (@lem1689576 _26059 _26061) (@lem1689558 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689581 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1689582 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term376 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060).
Proof. exact (@lem1689581 (real_le _26061 _26062) (term57 _26059 _26061) (term378 _26062 _26059 _26060)). Qed.
Lemma lem1689612 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term313 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060).
Proof. exact (TRANS (@lem1689577 _26061 _26062 _26059 _26060) (@lem1689582 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1689614 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term379 _26061 _26062 _26059 _26060) = (term380 _26061 _26062 _26059 _26060).
Proof. exact (MK_COMB (@lem1689613) (@lem1689612 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689644 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term377 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060).
Proof. exact (eq_refl (term377 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689645 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : ((term313 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060)) = ((term377 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060)).
Proof. exact (MK_COMB (@lem1689614 _26061 _26062 _26059 _26060) (@lem1689644 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689647 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1689648 (x : Prop) : (x = x) = True.
Proof. exact (@lem1689647 Prop x). Qed.
Lemma lem1689649 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : ((term377 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060)) = True.
Proof. exact (@lem1689648 (term377 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689650 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : ((term313 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060)) = True.
Proof. exact (TRANS (@lem1689645 _26061 _26062 _26059 _26060) (@lem1689649 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689651 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : True = ((term313 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060)).
Proof. exact (SYM (@lem1689650 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689652 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term313 _26061 _26062 _26059 _26060) = (term377 _26061 _26062 _26059 _26060).
Proof. exact (EQ_MP (@lem1689651 _26061 _26062 _26059 _26060) (@lem0)). Qed.
Lemma lem1689653 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : term377 _26061 _26062 _26059 _26060.
Proof. exact (EQ_MP (@lem1689652 _26061 _26062 _26059 _26060) (@lem1688849 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689655 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1689656 (_26059 : real) (_26060 : real) (_26061 : real) (_26062 : real) : (term377 _26061 _26062 _26059 _26060) = (term381 _26059 _26060 _26061 _26062).
Proof. exact (@lem1689655 (term382 _26061 _26062 _26059 _26060) (real_le _26061 _26062)). Qed.
Lemma lem1689658 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1689659 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term383 _26061 _26062 _26059 _26060) = (term384 _26061 _26062 _26059 _26060).
Proof. exact (@lem1689658 (term57 _26059 _26061) (term378 _26062 _26059 _26060)). Qed.
Lemma lem1689661 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689662 (_26059 : real) (_26061 : real) : (term72 _26059 _26061) = (_26059 = _26061).
Proof. exact (@lem1689661 (_26059 = _26061)). Qed.
Lemma lem1689663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1689664 (_26059 : real) (_26061 : real) : (term73 _26059 _26061) = (term74 _26059 _26061).
Proof. exact (MK_COMB (@lem1689663) (@lem1689662 _26059 _26061)). Qed.
Lemma lem1689666 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1689667 (_26062 : real) (_26059 : real) (_26060 : real) : (term385 _26062 _26059 _26060) = (term386 _26062 _26059 _26060).
Proof. exact (@lem1689666 (term57 _26060 _26062) (term296 _26059 _26060)). Qed.
Lemma lem1689669 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689670 (_26060 : real) (_26062 : real) : (term72 _26060 _26062) = (_26060 = _26062).
Proof. exact (@lem1689669 (_26060 = _26062)). Qed.
Lemma lem1689671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1689672 (_26060 : real) (_26062 : real) : (term73 _26060 _26062) = (term74 _26060 _26062).
Proof. exact (MK_COMB (@lem1689671) (@lem1689670 _26060 _26062)). Qed.
Lemma lem1689674 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1689675 (_26059 : real) (_26060 : real) : (term356 _26059 _26060) = (real_le _26059 _26060).
Proof. exact (@lem1689674 (real_le _26059 _26060)). Qed.
Lemma lem1689676 (_26062 : real) (_26059 : real) (_26060 : real) : (term386 _26062 _26059 _26060) = (term387 _26062 _26059 _26060).
Proof. exact (MK_COMB (@lem1689672 _26060 _26062) (@lem1689675 _26059 _26060)). Qed.
Lemma lem1689677 (_26062 : real) (_26059 : real) (_26060 : real) : (term385 _26062 _26059 _26060) = (term387 _26062 _26059 _26060).
Proof. exact (TRANS (@lem1689667 _26062 _26059 _26060) (@lem1689676 _26062 _26059 _26060)). Qed.
Lemma lem1689678 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term384 _26061 _26062 _26059 _26060) = (term388 _26061 _26062 _26059 _26060).
Proof. exact (MK_COMB (@lem1689664 _26059 _26061) (@lem1689677 _26062 _26059 _26060)). Qed.
Lemma lem1689679 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term383 _26061 _26062 _26059 _26060) = (term388 _26061 _26062 _26059 _26060).
Proof. exact (TRANS (@lem1689659 _26061 _26062 _26059 _26060) (@lem1689678 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1689681 (_26061 : real) (_26062 : real) (_26059 : real) (_26060 : real) : (term389 _26061 _26062 _26059 _26060) = (term390 _26061 _26062 _26059 _26060).
Proof. exact (MK_COMB (@lem1689680) (@lem1689679 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689682 (_26061 : real) (_26062 : real) : (real_le _26061 _26062) = (real_le _26061 _26062).
Proof. exact (eq_refl (real_le _26061 _26062)). Qed.
Lemma lem1689683 (_26059 : real) (_26060 : real) (_26061 : real) (_26062 : real) : (term381 _26059 _26060 _26061 _26062) = (term391 _26059 _26060 _26061 _26062).
Proof. exact (MK_COMB (@lem1689681 _26061 _26062 _26059 _26060) (@lem1689682 _26061 _26062)). Qed.
Lemma lem1689684 (_26059 : real) (_26060 : real) (_26061 : real) (_26062 : real) : (term377 _26061 _26062 _26059 _26060) = (term391 _26059 _26060 _26061 _26062).
Proof. exact (TRANS (@lem1689656 _26059 _26060 _26061 _26062) (@lem1689683 _26059 _26060 _26061 _26062)). Qed.
Lemma lem1689686 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term402 x y u v b.
Proof. exact (conj (@lem1688983 a u x v y b h2 h3) (@lem1689539 a u x v y b h1 h3)). Qed.
Lemma lem1689687 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term403 x y u v b.
Proof. exact (conj (@lem1688915 u x v y) (@lem1689686 a u x v y b h1 h2 h3)). Qed.
Lemma lem1689689 (_26059 : real) (_26060 : real) (_26061 : real) (_26062 : real) : term391 _26059 _26060 _26061 _26062.
Proof. exact (EQ_MP (@lem1689684 _26059 _26060 _26061 _26062) (@lem1689653 _26061 _26062 _26059 _26060)). Qed.
Lemma lem1689690 (u : real) (x : real) (v : real) (y : real) (b : real) : term404 u x v y b.
Proof. exact (@lem1689689 (term321 u x v y) (term31 u v b) (term321 u x v y) b). Qed.
Lemma lem1689693 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term167 u x v y b.
Proof. exact (@lem1689690 u x v y b (@lem1689687 a u x v y b h1 h2 h3)). Qed.
Lemma lem1689694 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term405 u x v y b.
Proof. exact (fun h0 : term285 u x v y b => @lem1689693 a u x v y b h1 h2 h3). Qed.
Lemma lem1689696 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1689697 (u : real) (x : real) (v : real) (y : real) (b : real) : (term405 u x v y b) = (term167 u x v y b).
Proof. exact (@lem1689696 (term167 u x v y b)). Qed.
Lemma lem1689698 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term167 u x v y b.
Proof. exact (EQ_MP (@lem1689697 u x v y b) (@lem1689694 a u x v y b h1 h2 h3)). Qed.
Lemma lem1689701 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1689703 (u : real) (x : real) (v : real) (y : real) (b : real) : (term285 u x v y b) = (term406 u x v y b).
Proof. exact (@lem1689701 (term167 u x v y b)). Qed.
Lemma lem1689706 (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term285 u x v y b) : term406 u x v y b.
Proof. exact (EQ_MP (@lem1689703 u x v y b) (@lem1687946 u x v y b h1)). Qed.
Lemma lem1689709 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (@lem1689706 u x v y b h3 (@lem1689698 a u x v y b h1 h2 h4)). Qed.
Lemma lem1689710 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : term109.
Proof. exact (fun h0 : ~ False => @lem1689709 a u x v y b h1 h2 h3 h4). Qed.
Lemma lem1689712 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1689713 : term109 = False.
Proof. exact (@lem1689712 False). Qed.
Lemma lem1689714 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689713) (@lem1689710 a u x v y b h1 h2 h3 h4)). Qed.
Lemma lem1689715 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : (term285 u x v y b) = False.
Proof. exact (prop_ext (fun h5 : term285 u x v y b => @lem1689714 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1687946 u x v y b h3)). Qed.
Lemma lem1689716 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689715 a u x v y b h1 h2 h3 h4) (@lem1687946 u x v y b h3)). Qed.
Lemma lem1689717 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : (term284 a u x v y) = False.
Proof. exact (prop_ext (fun h5 : term284 a u x v y => @lem1688830 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1687894 a u x v y h3)). Qed.
Lemma lem1689718 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689717 a u x v y b h1 h2 h3 h4) (@lem1687894 a u x v y h3)). Qed.
Lemma lem1689719 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : (term285 u x v y b) = False.
Proof. exact (prop_ext (fun h5 : term285 u x v y b => @lem1689716 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1687788 u x v y b h3)). Qed.
Lemma lem1689720 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689719 a u x v y b h1 h2 h3 h4) (@lem1687788 u x v y b h3)). Qed.
Lemma lem1689721 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : (term284 a u x v y) = False.
Proof. exact (prop_ext (fun h5 : term284 a u x v y => @lem1689718 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1687660 a u x v y h3)). Qed.
Lemma lem1689722 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689721 a u x v y b h1 h2 h3 h4) (@lem1687660 a u x v y h3)). Qed.
Lemma lem1689723 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : (term285 u x v y b) = False.
Proof. exact (prop_ext (fun h5 : term285 u x v y b => @lem1689720 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1687788 u x v y b h3)). Qed.
Lemma lem1689724 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689723 a u x v y b h1 h2 h3 h4) (@lem1687788 u x v y b h3)). Qed.
Lemma lem1689725 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : (term284 a u x v y) = False.
Proof. exact (prop_ext (fun h5 : term284 a u x v y => @lem1689722 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1687660 a u x v y h3)). Qed.
Lemma lem1689726 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689725 a u x v y b h1 h2 h3 h4) (@lem1687660 a u x v y h3)). Qed.
Lemma lem1689727 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : False.
Proof. exact (or_elim (@lem1687517 a u x v y b h3) (fun h0 : term284 a u x v y => @lem1689726 a u x v y b h1 h2 h0 h3) (fun h0 : term285 u x v y b => @lem1689724 a u x v y b h1 h2 h0 h3)). Qed.
Lemma lem1689728 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : (term170 a u x v y b) = False.
Proof. exact (prop_ext (fun h4 : term170 a u x v y b => @lem1689727 a u x v y b h1 h2 h3) (fun h4 : False => @lem1687516 a u x v y b h3)). Qed.
Lemma lem1689729 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1689728 a u x v y b h1 h2 h3) (@lem1687516 a u x v y b h3)). Qed.
Lemma lem1689730 (a : real) (u : real) (x : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term182 a u x y b) : False.
Proof. exact (ex_elim (@lem1687236 a u x y b h3) (fun v : real => fun h0 : term181 a u x y b v => @lem1689729 a u x v y b h1 h2 h0)). Qed.
Lemma lem1689731 (a : real) (x : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term189 a x y b) : False.
Proof. exact (ex_elim (@lem1687235 a x y b h3) (fun u : real => fun h0 : term188 a x y b u => @lem1689730 a u x y b h1 h2 h0)). Qed.
Lemma lem1689732 (a : real) (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term196 a x y) : False.
Proof. exact (ex_elim (@lem1687234 a x y h3) (fun b : real => fun h0 : term195 a x y b => @lem1689731 a x y b h1 h2 h0)). Qed.
Lemma lem1689733 (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term203 x y) : False.
Proof. exact (ex_elim (@lem1687233 x y h3) (fun a : real => fun h0 : term202 x y a => @lem1689732 a x y h1 h2 h0)). Qed.
Lemma lem1689734 (x : real) (h1 : term119) (h2 : term122) (h3 : term210 x) : False.
Proof. exact (ex_elim (@lem1687232 x h3) (fun y : real => fun h0 : term209 x y => @lem1689733 x y h1 h2 h0)). Qed.
Lemma lem1689735 (h1 : term119) (h2 : term122) (h3 : term125) : False.
Proof. exact (ex_elim (@lem1686999 h3) (fun x : real => fun h0 : term215 x => @lem1689734 x h1 h2 h0)). Qed.
Lemma lem1689736 (h1 : term122) (h2 : term125) : term130.
Proof. exact (fun h0 : term119 => @lem1689735 h0 h1 h2). Qed.
Lemma lem1689737 : term130 = term131.
Proof. exact (@lem69 term119). Qed.
Lemma lem1689738 (h1 : term122) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem1689737) (@lem1689736 h1 h2)). Qed.
Lemma lem1689739 (h1 : term125) : term134.
Proof. exact (fun h0 : term122 => @lem1689738 h0 h1). Qed.
Lemma lem1689740 : term136.
Proof. exact (fun h0 : term125 => @lem1689739 h0). Qed.
Lemma lem1689741 : term126.
Proof. exact (EQ_MP (@lem1686826) (@lem1689740)). Qed.
Lemma lem1689743 : term126.
Proof. exact (@lem1686479 (@lem1689741)). Qed.
Lemma lem1689744 (h1 : term125) : term133.
Proof. exact (@lem1689743 (@lem1686464 h1)). Qed.
Lemma lem1689745 (h1 : term125) : term130.
Proof. exact (@lem1689744 h1 (@lem1686459)). Qed.
Lemma lem1689746 (h1 : term125) : False.
Proof. exact (@lem1689745 h1 (@lem1686456)). Qed.
Lemma lem1689747 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem1689746 h1) (fun h2 : False => @lem1686464 h1)). Qed.
Lemma lem1689748 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem1689747 h1) (@lem1686464 h1)). Qed.
Lemma lem1689749 : term124.
Proof. exact (fun h0 : term125 => @lem1689748 h0). Qed.
Lemma lem1689750 : term123.
Proof. exact (EQ_MP (@lem1686463) (@lem1689749)). Qed.
