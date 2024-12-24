Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_PAIR_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import PAIR_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Lemma lem49921 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem49922 {_5131 _5132 : Type'} : (term1 _5131 _5132) = (term2 _5131 _5132).
Proof. exact (@lem49921 (term1 _5131 _5132)). Qed.
Lemma lem49923 {_5131 _5132 : Type'} : (term2 _5131 _5132) = (term1 _5131 _5132).
Proof. exact (SYM (@lem49922 _5131 _5132)). Qed.
Lemma lem49924 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : term3 _5131 _5132.
Proof. exact (h1). Qed.
Lemma lem49925 {_5131 _5132 : Type'} : term4 _5131 _5132.
Proof. exact (@lem48081 _5132 _5131). Qed.
Lemma lem49928 {_5131 _5132 : Type'} (h1 : term5 _5131 _5132) : term5 _5131 _5132.
Proof. exact (h1). Qed.
Lemma lem49929 {_5131 _5132 : Type'} : term6 _5131 _5132.
Proof. exact (fun h0 : term5 _5131 _5132 => @lem49928 _5131 _5132 h0). Qed.
Lemma lem49930 {_5131 _5132 : Type'} (h1 : term6 _5131 _5132) : term6 _5131 _5132.
Proof. exact (h1). Qed.
Lemma lem49931 {_5131 _5132 : Type'} (h1 : term5 _5131 _5132) : term5 _5131 _5132.
Proof. exact (h1). Qed.
Lemma lem49932 {_5131 _5132 : Type'} (h1 : term5 _5131 _5132) (h2 : term6 _5131 _5132) : term5 _5131 _5132.
Proof. exact (@lem49930 _5131 _5132 h2 (@lem49931 _5131 _5132 h1)). Qed.
Lemma lem49933 {_5131 _5132 : Type'} (h1 : term5 _5131 _5132) : term7 _5131 _5132.
Proof. exact (fun h0 : term6 _5131 _5132 => @lem49932 _5131 _5132 h1 h0). Qed.
Lemma lem49934 {_5131 _5132 : Type'} (h1 : term6 _5131 _5132) : term6 _5131 _5132.
Proof. exact (h1). Qed.
Lemma lem49935 {_5131 _5132 : Type'} (h1 : term5 _5131 _5132) (h2 : term6 _5131 _5132) : term5 _5131 _5132.
Proof. exact (@lem49933 _5131 _5132 h1 (@lem49934 _5131 _5132 h2)). Qed.
Lemma lem49936 {_5131 _5132 : Type'} (h1 : term6 _5131 _5132) : term6 _5131 _5132.
Proof. exact (fun h0 : term5 _5131 _5132 => @lem49935 _5131 _5132 h0 h1). Qed.
Lemma lem49937 {_5131 _5132 : Type'} : term8 _5131 _5132.
Proof. exact (fun h0 : term6 _5131 _5132 => @lem49936 _5131 _5132 h0). Qed.
Lemma lem49940 {_5131 _5132 : Type'} : term6 _5131 _5132.
Proof. exact (@lem49937 _5131 _5132 (@lem49929 _5131 _5132)). Qed.
Lemma lem49941 {_5131 _5132 : Type'} : term6 _5131 _5132.
Proof. exact (@lem49940 _5131 _5132). Qed.
Lemma lem49961 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem49962 {_5131 _5132 : Type'} : (term9 _5131 _5132) = (term10 _5131 _5132).
Proof. exact (@lem49961 (term4 _5131 _5132)). Qed.
Lemma lem49967 {_5131 _5132 : Type'} : (term11 _5131 _5132) = (term11 _5131 _5132).
Proof. exact (eq_refl (term11 _5131 _5132)). Qed.
Lemma lem49974 {_5131 _5132 : Type'} : (term5 _5131 _5132) = (term12 _5131 _5132).
Proof. exact (MK_COMB (@lem49967 _5131 _5132) (@lem49962 _5131 _5132)). Qed.
Lemma lem49975 {_5131 _5132 : Type'} (x : prod _5132 _5131) : ((term13 _5131 _5132 x) = x) = ((term13 _5131 _5132 x) = x).
Proof. exact (eq_refl ((term13 _5131 _5132 x) = x)). Qed.
Lemma lem49976 {_5131 _5132 : Type'} : (term14 _5131 _5132) = (term14 _5131 _5132).
Proof. exact (fun_ext (fun x : prod _5132 _5131 => @lem49975 _5131 _5132 x)). Qed.
Lemma lem49977 {_5131 _5132 : Type'} : (@all (prod _5132 _5131)) = (@all (prod _5132 _5131)).
Proof. exact (eq_refl (@all (prod _5132 _5131))). Qed.
Lemma lem49978 {_5131 _5132 : Type'} : (term4 _5131 _5132) = (term4 _5131 _5132).
Proof. exact (MK_COMB (@lem49977 _5131 _5132) (@lem49976 _5131 _5132)). Qed.
Lemma lem49979 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem49980 {_5131 _5132 : Type'} : (term10 _5131 _5132) = (term10 _5131 _5132).
Proof. exact (MK_COMB (@lem49979) (@lem49978 _5131 _5132)). Qed.
Lemma lem49981 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term15 _5131 _5132 P p1 p2) = (term15 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term15 _5131 _5132 P p1 p2)). Qed.
Lemma lem49982 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term16 _5131 _5132 P p1) = (term16 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem49981 _5131 _5132 P p1 p2)). Qed.
Lemma lem49983 {_5131 : Type'} : (@ex _5131) = (@ex _5131).
Proof. exact (eq_refl (@ex _5131)). Qed.
Lemma lem49984 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term17 _5131 _5132 P p1) = (term17 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem49983 _5131) (@lem49982 _5131 _5132 P p1)). Qed.
Lemma lem49985 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term18 _5131 _5132 P) = (term18 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem49984 _5131 _5132 P p1)). Qed.
Lemma lem49986 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem49987 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term19 _5131 _5132 P) = (term19 _5131 _5132 P).
Proof. exact (MK_COMB (@lem49986 _5132) (@lem49985 _5131 _5132 P)). Qed.
Lemma lem49988 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem49989 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term20 _5131 _5132 P) = (term20 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem49988 _5131 _5132 P p)). Qed.
Lemma lem49990 {_5131 _5132 : Type'} : (@ex (prod _5132 _5131)) = (@ex (prod _5132 _5131)).
Proof. exact (eq_refl (@ex (prod _5132 _5131))). Qed.
Lemma lem49991 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term21 _5131 _5132 P) = (term21 _5131 _5132 P).
Proof. exact (MK_COMB (@lem49990 _5131 _5132) (@lem49989 _5131 _5132 P)). Qed.
Lemma lem49992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49993 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term22 _5131 _5132 P) = (term22 _5131 _5132 P).
Proof. exact (MK_COMB (@lem49992) (@lem49991 _5131 _5132 P)). Qed.
Lemma lem49994 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : ((term21 _5131 _5132 P) = (term19 _5131 _5132 P)) = ((term21 _5131 _5132 P) = (term19 _5131 _5132 P)).
Proof. exact (MK_COMB (@lem49993 _5131 _5132 P) (@lem49987 _5131 _5132 P)). Qed.
Lemma lem49995 {_5131 _5132 : Type'} : (term23 _5131 _5132) = (term23 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem49994 _5131 _5132 P)). Qed.
Lemma lem49996 {_5131 _5132 : Type'} : (@all ((prod _5132 _5131) -> Prop)) = (@all ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@all ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem49997 {_5131 _5132 : Type'} : (term1 _5131 _5132) = (term1 _5131 _5132).
Proof. exact (MK_COMB (@lem49996 _5131 _5132) (@lem49995 _5131 _5132)). Qed.
Lemma lem49998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem49999 {_5131 _5132 : Type'} : (term3 _5131 _5132) = (term3 _5131 _5132).
Proof. exact (MK_COMB (@lem49998) (@lem49997 _5131 _5132)). Qed.
Lemma lem50000 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem50001 {_5131 _5132 : Type'} : (term11 _5131 _5132) = (term11 _5131 _5132).
Proof. exact (MK_COMB (@lem50000) (@lem49999 _5131 _5132)). Qed.
Lemma lem50002 {_5131 _5132 : Type'} : (term12 _5131 _5132) = (term12 _5131 _5132).
Proof. exact (MK_COMB (@lem50001 _5131 _5132) (@lem49980 _5131 _5132)). Qed.
Lemma lem50037 {_5131 _5132 : Type'} : (term5 _5131 _5132) = (term12 _5131 _5132).
Proof. exact (TRANS (@lem49974 _5131 _5132) (@lem50002 _5131 _5132)). Qed.
Lemma lem50038 {_5131 _5132 : Type'} : (term12 _5131 _5132) = (term5 _5131 _5132).
Proof. exact (SYM (@lem50037 _5131 _5132)). Qed.
Lemma lem50039 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : term3 _5131 _5132.
Proof. exact (h1). Qed.
Lemma lem50040 {_5131 _5132 : Type'} (h1 : term4 _5131 _5132) : term4 _5131 _5132.
Proof. exact (h1). Qed.
Lemma lem50042 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem50043 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term24 _5131 _5132 P) = (term25 _5131 _5132 P).
Proof. exact (@lem18394 (prod _5132 _5131) P). Qed.
Lemma lem50044 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term26 _5131 _5132 P) = (term27 _5131 _5132 P).
Proof. exact (@lem50043 _5131 _5132 (term20 _5131 _5132 P)). Qed.
Lemma lem50045 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (term28 _5131 _5132 P p) = (P p).
Proof. exact (eq_refl (term28 _5131 _5132 P p)). Qed.
Lemma lem50046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem50048 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (term29 _5131 _5132 P p) = (term30 _5131 _5132 P p).
Proof. exact (MK_COMB (@lem50046) (@lem50045 _5131 _5132 P p)). Qed.
Lemma lem50049 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term31 _5131 _5132 P) = (term32 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem50048 _5131 _5132 P p)). Qed.
Lemma lem50050 {_5131 _5132 : Type'} : (@all (prod _5132 _5131)) = (@all (prod _5132 _5131)).
Proof. exact (eq_refl (@all (prod _5132 _5131))). Qed.
Lemma lem50051 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term27 _5131 _5132 P) = (term25 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50050 _5131 _5132) (@lem50049 _5131 _5132 P)). Qed.
Lemma lem50052 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term26 _5131 _5132 P) = (term25 _5131 _5132 P).
Proof. exact (TRANS (@lem50044 _5131 _5132 P) (@lem50051 _5131 _5132 P)). Qed.
Lemma lem50053 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term20 _5131 _5132 P) = (term20 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem50042 _5131 _5132 P p)). Qed.
Lemma lem50054 {_5131 _5132 : Type'} : (@ex (prod _5132 _5131)) = (@ex (prod _5132 _5131)).
Proof. exact (eq_refl (@ex (prod _5132 _5131))). Qed.
Lemma lem50055 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term21 _5131 _5132 P) = (term21 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50054 _5131 _5132) (@lem50053 _5131 _5132 P)). Qed.
Lemma lem50057 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term15 _5131 _5132 P p1 p2) = (term15 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term15 _5131 _5132 P p1 p2)). Qed.
Lemma lem50058 {_5131 : Type'} (P : _5131 -> Prop) : (term33 _5131 P) = (term34 _5131 P).
Proof. exact (@lem18394 _5131 P). Qed.
Lemma lem50059 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term35 _5131 _5132 P p1) = (term36 _5131 _5132 P p1).
Proof. exact (@lem50058 _5131 (term16 _5131 _5132 P p1)). Qed.
Lemma lem50060 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term37 _5131 _5132 P p1 p2) = (term15 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term37 _5131 _5132 P p1 p2)). Qed.
Lemma lem50061 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem50063 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term38 _5131 _5132 P p1 p2) = (term39 _5131 _5132 P p1 p2).
Proof. exact (MK_COMB (@lem50061) (@lem50060 _5131 _5132 P p1 p2)). Qed.
Lemma lem50064 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term40 _5131 _5132 P p1) = (term41 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50063 _5131 _5132 P p1 p2)). Qed.
Lemma lem50065 {_5131 : Type'} : (@all _5131) = (@all _5131).
Proof. exact (eq_refl (@all _5131)). Qed.
Lemma lem50066 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term36 _5131 _5132 P p1) = (term42 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50065 _5131) (@lem50064 _5131 _5132 P p1)). Qed.
Lemma lem50067 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term35 _5131 _5132 P p1) = (term42 _5131 _5132 P p1).
Proof. exact (TRANS (@lem50059 _5131 _5132 P p1) (@lem50066 _5131 _5132 P p1)). Qed.
Lemma lem50068 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term16 _5131 _5132 P p1) = (term16 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50057 _5131 _5132 P p1 p2)). Qed.
Lemma lem50069 {_5131 : Type'} : (@ex _5131) = (@ex _5131).
Proof. exact (eq_refl (@ex _5131)). Qed.
Lemma lem50070 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term17 _5131 _5132 P p1) = (term17 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50069 _5131) (@lem50068 _5131 _5132 P p1)). Qed.
Lemma lem50071 {_5132 : Type'} (P : _5132 -> Prop) : (term33 _5132 P) = (term34 _5132 P).
Proof. exact (@lem18394 _5132 P). Qed.
Lemma lem50072 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term43 _5131 _5132 P) = (term44 _5131 _5132 P).
Proof. exact (@lem50071 _5132 (term18 _5131 _5132 P)). Qed.
Lemma lem50073 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term45 _5131 _5132 P p1) = (term17 _5131 _5132 P p1).
Proof. exact (eq_refl (term45 _5131 _5132 P p1)). Qed.
Lemma lem50074 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem50075 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term46 _5131 _5132 P p1) = (term35 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50074) (@lem50073 _5131 _5132 P p1)). Qed.
Lemma lem50076 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term46 _5131 _5132 P p1) = (term42 _5131 _5132 P p1).
Proof. exact (TRANS (@lem50075 _5131 _5132 P p1) (@lem50067 _5131 _5132 P p1)). Qed.
Lemma lem50077 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term47 _5131 _5132 P) = (term48 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50076 _5131 _5132 P p1)). Qed.
Lemma lem50078 {_5132 : Type'} : (@all _5132) = (@all _5132).
Proof. exact (eq_refl (@all _5132)). Qed.
Lemma lem50079 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term44 _5131 _5132 P) = (term49 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50078 _5132) (@lem50077 _5131 _5132 P)). Qed.
Lemma lem50080 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term43 _5131 _5132 P) = (term49 _5131 _5132 P).
Proof. exact (TRANS (@lem50072 _5131 _5132 P) (@lem50079 _5131 _5132 P)). Qed.
Lemma lem50081 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term18 _5131 _5132 P) = (term18 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50070 _5131 _5132 P p1)). Qed.
Lemma lem50082 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem50083 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term19 _5131 _5132 P) = (term19 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50082 _5132) (@lem50081 _5131 _5132 P)). Qed.
Lemma lem50084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem50085 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term50 _5131 _5132 P) = (term51 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50084) (@lem50052 _5131 _5132 P)). Qed.
Lemma lem50086 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term52 _5131 _5132 P) = (term53 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50085 _5131 _5132 P) (@lem50083 _5131 _5132 P)). Qed.
Lemma lem50087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem50088 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term54 _5131 _5132 P) = (term54 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50087) (@lem50055 _5131 _5132 P)). Qed.
Lemma lem50089 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term55 _5131 _5132 P) = (term56 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50088 _5131 _5132 P) (@lem50080 _5131 _5132 P)). Qed.
Lemma lem50090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50091 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term57 _5131 _5132 P) = (term58 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50090) (@lem50089 _5131 _5132 P)). Qed.
Lemma lem50092 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term59 _5131 _5132 P) = (term60 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50091 _5131 _5132 P) (@lem50086 _5131 _5132 P)). Qed.
Lemma lem50093 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term61 _5131 _5132 P) = (term59 _5131 _5132 P).
Proof. exact (@lem17646 (term21 _5131 _5132 P) (term19 _5131 _5132 P)). Qed.
Lemma lem50094 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term61 _5131 _5132 P) = (term60 _5131 _5132 P).
Proof. exact (TRANS (@lem50093 _5131 _5132 P) (@lem50092 _5131 _5132 P)). Qed.
Lemma lem50095 {_5131 _5132 : Type'} (P : type330 _5131 _5132) : (term62 _5131 _5132 P) = (term63 _5131 _5132 P).
Proof. exact (@lem18392 (type1223 _5131 _5132) P). Qed.
Lemma lem50096 {_5131 _5132 : Type'} : (term3 _5131 _5132) = (term64 _5131 _5132).
Proof. exact (@lem50095 _5131 _5132 (term23 _5131 _5132)). Qed.
Lemma lem50097 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term65 _5131 _5132 P) = ((term21 _5131 _5132 P) = (term19 _5131 _5132 P)).
Proof. exact (eq_refl (term65 _5131 _5132 P)). Qed.
Lemma lem50098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem50099 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term66 _5131 _5132 P) = (term61 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50098) (@lem50097 _5131 _5132 P)). Qed.
Lemma lem50100 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term66 _5131 _5132 P) = (term60 _5131 _5132 P).
Proof. exact (TRANS (@lem50099 _5131 _5132 P) (@lem50094 _5131 _5132 P)). Qed.
Lemma lem50101 {_5131 _5132 : Type'} : (term67 _5131 _5132) = (term68 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50100 _5131 _5132 P)). Qed.
Lemma lem50102 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50103 {_5131 _5132 : Type'} : (term64 _5131 _5132) = (term69 _5131 _5132).
Proof. exact (MK_COMB (@lem50102 _5131 _5132) (@lem50101 _5131 _5132)). Qed.
Lemma lem50104 {_5131 _5132 : Type'} : (term3 _5131 _5132) = (term69 _5131 _5132).
Proof. exact (TRANS (@lem50096 _5131 _5132) (@lem50103 _5131 _5132)). Qed.
Lemma lem50106 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem50107 {_5131 _5132 : Type'} (P : type330 _5131 _5132) (Q : type330 _5131 _5132) : (term72 _5131 _5132 P Q) = (term73 _5131 _5132 P Q).
Proof. exact (@lem50106 (type1223 _5131 _5132) P Q). Qed.
Lemma lem50108 {_5131 _5132 : Type'} : (term74 _5131 _5132) = (term75 _5131 _5132).
Proof. exact (@lem50107 _5131 _5132 (term76 _5131 _5132) (term77 _5131 _5132)). Qed.
Lemma lem50109 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term78 _5131 _5132 P) = (term56 _5131 _5132 P).
Proof. exact (eq_refl (term78 _5131 _5132 P)). Qed.
Lemma lem50110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50111 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term79 _5131 _5132 P) = (term58 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50110) (@lem50109 _5131 _5132 P)). Qed.
Lemma lem50112 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term80 _5131 _5132 P) = (term53 _5131 _5132 P).
Proof. exact (eq_refl (term80 _5131 _5132 P)). Qed.
Lemma lem50113 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term81 _5131 _5132 P) = (term60 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50111 _5131 _5132 P) (@lem50112 _5131 _5132 P)). Qed.
Lemma lem50114 {_5131 _5132 : Type'} : (term82 _5131 _5132) = (term68 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50113 _5131 _5132 P)). Qed.
Lemma lem50115 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50116 {_5131 _5132 : Type'} : (term74 _5131 _5132) = (term69 _5131 _5132).
Proof. exact (MK_COMB (@lem50115 _5131 _5132) (@lem50114 _5131 _5132)). Qed.
Lemma lem50117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50118 {_5131 _5132 : Type'} : (term83 _5131 _5132) = (term84 _5131 _5132).
Proof. exact (MK_COMB (@lem50117) (@lem50116 _5131 _5132)). Qed.
Lemma lem50119 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term78 _5131 _5132 P) = (term56 _5131 _5132 P).
Proof. exact (eq_refl (term78 _5131 _5132 P)). Qed.
Lemma lem50120 {_5131 _5132 : Type'} : (term85 _5131 _5132) = (term76 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50119 _5131 _5132 P)). Qed.
Lemma lem50121 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50122 {_5131 _5132 : Type'} : (term86 _5131 _5132) = (term87 _5131 _5132).
Proof. exact (MK_COMB (@lem50121 _5131 _5132) (@lem50120 _5131 _5132)). Qed.
Lemma lem50123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50124 {_5131 _5132 : Type'} : (term88 _5131 _5132) = (term89 _5131 _5132).
Proof. exact (MK_COMB (@lem50123) (@lem50122 _5131 _5132)). Qed.
Lemma lem50125 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term80 _5131 _5132 P) = (term53 _5131 _5132 P).
Proof. exact (eq_refl (term80 _5131 _5132 P)). Qed.
Lemma lem50126 {_5131 _5132 : Type'} : (term90 _5131 _5132) = (term77 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50125 _5131 _5132 P)). Qed.
Lemma lem50127 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50128 {_5131 _5132 : Type'} : (term91 _5131 _5132) = (term92 _5131 _5132).
Proof. exact (MK_COMB (@lem50127 _5131 _5132) (@lem50126 _5131 _5132)). Qed.
Lemma lem50129 {_5131 _5132 : Type'} : (term75 _5131 _5132) = (term93 _5131 _5132).
Proof. exact (MK_COMB (@lem50124 _5131 _5132) (@lem50128 _5131 _5132)). Qed.
Lemma lem50130 {_5131 _5132 : Type'} : ((term74 _5131 _5132) = (term75 _5131 _5132)) = ((term69 _5131 _5132) = (term93 _5131 _5132)).
Proof. exact (MK_COMB (@lem50118 _5131 _5132) (@lem50129 _5131 _5132)). Qed.
Lemma lem50131 {_5131 _5132 : Type'} : (term69 _5131 _5132) = (term93 _5131 _5132).
Proof. exact (EQ_MP (@lem50130 _5131 _5132) (@lem50108 _5131 _5132)). Qed.
Lemma lem50253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem50254 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (Q : Prop) : (term96 _5131 _5132 P Q) = (term97 _5131 _5132 P Q).
Proof. exact (@lem50253 (prod _5132 _5131) P Q). Qed.
Lemma lem50255 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term56 _5131 _5132 P) = (term98 _5131 _5132 P).
Proof. exact (@lem50254 _5131 _5132 P (term49 _5131 _5132 P)). Qed.
Lemma lem50256 {_5131 _5132 : Type'} : (term76 _5131 _5132) = (term99 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50255 _5131 _5132 P)). Qed.
Lemma lem50257 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50258 {_5131 _5132 : Type'} : (term87 _5131 _5132) = (term100 _5131 _5132).
Proof. exact (MK_COMB (@lem50257 _5131 _5132) (@lem50256 _5131 _5132)). Qed.
Lemma lem50259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50260 {_5131 _5132 : Type'} : (term89 _5131 _5132) = (term101 _5131 _5132).
Proof. exact (MK_COMB (@lem50259) (@lem50258 _5131 _5132)). Qed.
Lemma lem50262 {A : Type'} (P : Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem50263 {_5132 : Type'} (P : Prop) (Q : _5132 -> Prop) : (term102 _5132 P Q) = (term103 _5132 P Q).
Proof. exact (@lem50262 _5132 P Q). Qed.
Lemma lem50264 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term104 _5131 _5132 P) = (term105 _5131 _5132 P).
Proof. exact (@lem50263 _5132 (term25 _5131 _5132 P) (term18 _5131 _5132 P)). Qed.
Lemma lem50265 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term45 _5131 _5132 P p1) = (term17 _5131 _5132 P p1).
Proof. exact (eq_refl (term45 _5131 _5132 P p1)). Qed.
Lemma lem50266 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term106 _5131 _5132 P) = (term18 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50265 _5131 _5132 P p1)). Qed.
Lemma lem50267 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem50268 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term107 _5131 _5132 P) = (term19 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50267 _5132) (@lem50266 _5131 _5132 P)). Qed.
Lemma lem50269 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term51 _5131 _5132 P) = (term51 _5131 _5132 P).
Proof. exact (eq_refl (term51 _5131 _5132 P)). Qed.
Lemma lem50270 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term104 _5131 _5132 P) = (term53 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50269 _5131 _5132 P) (@lem50268 _5131 _5132 P)). Qed.
Lemma lem50271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50272 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term108 _5131 _5132 P) = (term109 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50271) (@lem50270 _5131 _5132 P)). Qed.
Lemma lem50273 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term45 _5131 _5132 P p1) = (term17 _5131 _5132 P p1).
Proof. exact (eq_refl (term45 _5131 _5132 P p1)). Qed.
Lemma lem50274 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term51 _5131 _5132 P) = (term51 _5131 _5132 P).
Proof. exact (eq_refl (term51 _5131 _5132 P)). Qed.
Lemma lem50275 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term110 _5131 _5132 P p1) = (term111 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50274 _5131 _5132 P) (@lem50273 _5131 _5132 P p1)). Qed.
Lemma lem50276 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term112 _5131 _5132 P) = (term113 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50275 _5131 _5132 P p1)). Qed.
Lemma lem50277 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem50278 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term105 _5131 _5132 P) = (term114 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50277 _5132) (@lem50276 _5131 _5132 P)). Qed.
Lemma lem50279 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : ((term104 _5131 _5132 P) = (term105 _5131 _5132 P)) = ((term53 _5131 _5132 P) = (term114 _5131 _5132 P)).
Proof. exact (MK_COMB (@lem50272 _5131 _5132 P) (@lem50278 _5131 _5132 P)). Qed.
Lemma lem50280 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term53 _5131 _5132 P) = (term114 _5131 _5132 P).
Proof. exact (EQ_MP (@lem50279 _5131 _5132 P) (@lem50264 _5131 _5132 P)). Qed.
Lemma lem50282 {A : Type'} (P : Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem50283 {_5131 : Type'} (P : Prop) (Q : _5131 -> Prop) : (term102 _5131 P Q) = (term103 _5131 P Q).
Proof. exact (@lem50282 _5131 P Q). Qed.
Lemma lem50284 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term115 _5131 _5132 P p1) = (term116 _5131 _5132 P p1).
Proof. exact (@lem50283 _5131 (term25 _5131 _5132 P) (term16 _5131 _5132 P p1)). Qed.
Lemma lem50285 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term37 _5131 _5132 P p1 p2) = (term15 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term37 _5131 _5132 P p1 p2)). Qed.
Lemma lem50286 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term117 _5131 _5132 P p1) = (term16 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50285 _5131 _5132 P p1 p2)). Qed.
Lemma lem50287 {_5131 : Type'} : (@ex _5131) = (@ex _5131).
Proof. exact (eq_refl (@ex _5131)). Qed.
Lemma lem50288 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term118 _5131 _5132 P p1) = (term17 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50287 _5131) (@lem50286 _5131 _5132 P p1)). Qed.
Lemma lem50289 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term51 _5131 _5132 P) = (term51 _5131 _5132 P).
Proof. exact (eq_refl (term51 _5131 _5132 P)). Qed.
Lemma lem50290 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term115 _5131 _5132 P p1) = (term111 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50289 _5131 _5132 P) (@lem50288 _5131 _5132 P p1)). Qed.
Lemma lem50291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50292 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term119 _5131 _5132 P p1) = (term120 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50291) (@lem50290 _5131 _5132 P p1)). Qed.
Lemma lem50293 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term37 _5131 _5132 P p1 p2) = (term15 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term37 _5131 _5132 P p1 p2)). Qed.
Lemma lem50294 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term51 _5131 _5132 P) = (term51 _5131 _5132 P).
Proof. exact (eq_refl (term51 _5131 _5132 P)). Qed.
Lemma lem50295 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term121 _5131 _5132 P p1 p2) = (term122 _5131 _5132 P p1 p2).
Proof. exact (MK_COMB (@lem50294 _5131 _5132 P) (@lem50293 _5131 _5132 P p1 p2)). Qed.
Lemma lem50296 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term123 _5131 _5132 P p1) = (term124 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50295 _5131 _5132 P p1 p2)). Qed.
Lemma lem50297 {_5131 : Type'} : (@ex _5131) = (@ex _5131).
Proof. exact (eq_refl (@ex _5131)). Qed.
Lemma lem50298 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term116 _5131 _5132 P p1) = (term125 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50297 _5131) (@lem50296 _5131 _5132 P p1)). Qed.
Lemma lem50299 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : ((term115 _5131 _5132 P p1) = (term116 _5131 _5132 P p1)) = ((term111 _5131 _5132 P p1) = (term125 _5131 _5132 P p1)).
Proof. exact (MK_COMB (@lem50292 _5131 _5132 P p1) (@lem50298 _5131 _5132 P p1)). Qed.
Lemma lem50300 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term111 _5131 _5132 P p1) = (term125 _5131 _5132 P p1).
Proof. exact (EQ_MP (@lem50299 _5131 _5132 P p1) (@lem50284 _5131 _5132 P p1)). Qed.
Lemma lem50301 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term113 _5131 _5132 P) = (term126 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50300 _5131 _5132 P p1)). Qed.
Lemma lem50302 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem50303 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term114 _5131 _5132 P) = (term127 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50302 _5132) (@lem50301 _5131 _5132 P)). Qed.
Lemma lem50304 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term53 _5131 _5132 P) = (term127 _5131 _5132 P).
Proof. exact (TRANS (@lem50280 _5131 _5132 P) (@lem50303 _5131 _5132 P)). Qed.
Lemma lem50305 {_5131 _5132 : Type'} : (term77 _5131 _5132) = (term128 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50304 _5131 _5132 P)). Qed.
Lemma lem50306 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50307 {_5131 _5132 : Type'} : (term92 _5131 _5132) = (term129 _5131 _5132).
Proof. exact (MK_COMB (@lem50306 _5131 _5132) (@lem50305 _5131 _5132)). Qed.
Lemma lem50308 {_5131 _5132 : Type'} : (term93 _5131 _5132) = (term130 _5131 _5132).
Proof. exact (MK_COMB (@lem50260 _5131 _5132) (@lem50307 _5131 _5132)). Qed.
Lemma lem50310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem50311 {_5131 _5132 : Type'} (P : type330 _5131 _5132) (Q : type330 _5131 _5132) : (term73 _5131 _5132 P Q) = (term72 _5131 _5132 P Q).
Proof. exact (@lem50310 (type1223 _5131 _5132) P Q). Qed.
Lemma lem50312 {_5131 _5132 : Type'} : (term131 _5131 _5132) = (term132 _5131 _5132).
Proof. exact (@lem50311 _5131 _5132 (term99 _5131 _5132) (term128 _5131 _5132)). Qed.
Lemma lem50313 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term133 _5131 _5132 P) = (term98 _5131 _5132 P).
Proof. exact (eq_refl (term133 _5131 _5132 P)). Qed.
Lemma lem50314 {_5131 _5132 : Type'} : (term134 _5131 _5132) = (term99 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50313 _5131 _5132 P)). Qed.
Lemma lem50315 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50316 {_5131 _5132 : Type'} : (term135 _5131 _5132) = (term100 _5131 _5132).
Proof. exact (MK_COMB (@lem50315 _5131 _5132) (@lem50314 _5131 _5132)). Qed.
Lemma lem50317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50318 {_5131 _5132 : Type'} : (term136 _5131 _5132) = (term101 _5131 _5132).
Proof. exact (MK_COMB (@lem50317) (@lem50316 _5131 _5132)). Qed.
Lemma lem50319 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term137 _5131 _5132 P) = (term127 _5131 _5132 P).
Proof. exact (eq_refl (term137 _5131 _5132 P)). Qed.
Lemma lem50320 {_5131 _5132 : Type'} : (term138 _5131 _5132) = (term128 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50319 _5131 _5132 P)). Qed.
Lemma lem50321 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50322 {_5131 _5132 : Type'} : (term139 _5131 _5132) = (term129 _5131 _5132).
Proof. exact (MK_COMB (@lem50321 _5131 _5132) (@lem50320 _5131 _5132)). Qed.
Lemma lem50323 {_5131 _5132 : Type'} : (term131 _5131 _5132) = (term130 _5131 _5132).
Proof. exact (MK_COMB (@lem50318 _5131 _5132) (@lem50322 _5131 _5132)). Qed.
Lemma lem50324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50325 {_5131 _5132 : Type'} : (term140 _5131 _5132) = (term141 _5131 _5132).
Proof. exact (MK_COMB (@lem50324) (@lem50323 _5131 _5132)). Qed.
Lemma lem50326 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term133 _5131 _5132 P) = (term98 _5131 _5132 P).
Proof. exact (eq_refl (term133 _5131 _5132 P)). Qed.
Lemma lem50327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50328 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term142 _5131 _5132 P) = (term143 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50327) (@lem50326 _5131 _5132 P)). Qed.
Lemma lem50329 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term137 _5131 _5132 P) = (term127 _5131 _5132 P).
Proof. exact (eq_refl (term137 _5131 _5132 P)). Qed.
Lemma lem50330 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term144 _5131 _5132 P) = (term145 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50328 _5131 _5132 P) (@lem50329 _5131 _5132 P)). Qed.
Lemma lem50331 {_5131 _5132 : Type'} : (term146 _5131 _5132) = (term147 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50330 _5131 _5132 P)). Qed.
Lemma lem50332 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50333 {_5131 _5132 : Type'} : (term132 _5131 _5132) = (term148 _5131 _5132).
Proof. exact (MK_COMB (@lem50332 _5131 _5132) (@lem50331 _5131 _5132)). Qed.
Lemma lem50334 {_5131 _5132 : Type'} : ((term131 _5131 _5132) = (term132 _5131 _5132)) = ((term130 _5131 _5132) = (term148 _5131 _5132)).
Proof. exact (MK_COMB (@lem50325 _5131 _5132) (@lem50333 _5131 _5132)). Qed.
Lemma lem50335 {_5131 _5132 : Type'} : (term130 _5131 _5132) = (term148 _5131 _5132).
Proof. exact (EQ_MP (@lem50334 _5131 _5132) (@lem50312 _5131 _5132)). Qed.
Lemma lem50339 {A : Type'} (P : A -> Prop) (Q : Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem50340 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (Q : Prop) : (term151 _5131 _5132 P Q) = (term152 _5131 _5132 P Q).
Proof. exact (@lem50339 (prod _5132 _5131) P Q). Qed.
Lemma lem50341 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term153 _5131 _5132 P) = (term154 _5131 _5132 P).
Proof. exact (@lem50340 _5131 _5132 (term155 _5131 _5132 P) (term127 _5131 _5132 P)). Qed.
Lemma lem50342 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term156 _5131 _5132 P p) = (term157 _5131 _5132 p P).
Proof. exact (eq_refl (term156 _5131 _5132 P p)). Qed.
Lemma lem50343 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term158 _5131 _5132 P) = (term155 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem50342 _5131 _5132 p P)). Qed.
Lemma lem50344 {_5131 _5132 : Type'} : (@ex (prod _5132 _5131)) = (@ex (prod _5132 _5131)).
Proof. exact (eq_refl (@ex (prod _5132 _5131))). Qed.
Lemma lem50345 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term159 _5131 _5132 P) = (term98 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50344 _5131 _5132) (@lem50343 _5131 _5132 P)). Qed.
Lemma lem50346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50347 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term160 _5131 _5132 P) = (term143 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50346) (@lem50345 _5131 _5132 P)). Qed.
Lemma lem50348 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term127 _5131 _5132 P) = (term127 _5131 _5132 P).
Proof. exact (eq_refl (term127 _5131 _5132 P)). Qed.
Lemma lem50349 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term153 _5131 _5132 P) = (term145 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50347 _5131 _5132 P) (@lem50348 _5131 _5132 P)). Qed.
Lemma lem50350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50351 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term161 _5131 _5132 P) = (term162 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50350) (@lem50349 _5131 _5132 P)). Qed.
Lemma lem50352 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term156 _5131 _5132 P p) = (term157 _5131 _5132 p P).
Proof. exact (eq_refl (term156 _5131 _5132 P p)). Qed.
Lemma lem50353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50354 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term163 _5131 _5132 P p) = (term164 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50353) (@lem50352 _5131 _5132 p P)). Qed.
Lemma lem50355 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term127 _5131 _5132 P) = (term127 _5131 _5132 P).
Proof. exact (eq_refl (term127 _5131 _5132 P)). Qed.
Lemma lem50356 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term165 _5131 _5132 p P) = (term166 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50354 _5131 _5132 p P) (@lem50355 _5131 _5132 P)). Qed.
Lemma lem50357 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term167 _5131 _5132 P) = (term168 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem50356 _5131 _5132 p P)). Qed.
Lemma lem50358 {_5131 _5132 : Type'} : (@ex (prod _5132 _5131)) = (@ex (prod _5132 _5131)).
Proof. exact (eq_refl (@ex (prod _5132 _5131))). Qed.
Lemma lem50359 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term154 _5131 _5132 P) = (term169 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50358 _5131 _5132) (@lem50357 _5131 _5132 P)). Qed.
Lemma lem50360 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : ((term153 _5131 _5132 P) = (term154 _5131 _5132 P)) = ((term145 _5131 _5132 P) = (term169 _5131 _5132 P)).
Proof. exact (MK_COMB (@lem50351 _5131 _5132 P) (@lem50359 _5131 _5132 P)). Qed.
Lemma lem50361 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term145 _5131 _5132 P) = (term169 _5131 _5132 P).
Proof. exact (EQ_MP (@lem50360 _5131 _5132 P) (@lem50341 _5131 _5132 P)). Qed.
Lemma lem50363 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem50364 {_5132 : Type'} (P : Prop) (Q : _5132 -> Prop) : (term170 _5132 P Q) = (term171 _5132 P Q).
Proof. exact (@lem50363 _5132 P Q). Qed.
Lemma lem50365 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term172 _5131 _5132 p P) = (term173 _5131 _5132 p P).
Proof. exact (@lem50364 _5132 (term157 _5131 _5132 p P) (term126 _5131 _5132 P)). Qed.
Lemma lem50366 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term174 _5131 _5132 P p1) = (term125 _5131 _5132 P p1).
Proof. exact (eq_refl (term174 _5131 _5132 P p1)). Qed.
Lemma lem50367 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term175 _5131 _5132 P) = (term126 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50366 _5131 _5132 P p1)). Qed.
Lemma lem50368 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem50369 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term176 _5131 _5132 P) = (term127 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50368 _5132) (@lem50367 _5131 _5132 P)). Qed.
Lemma lem50370 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term164 _5131 _5132 p P) = (term164 _5131 _5132 p P).
Proof. exact (eq_refl (term164 _5131 _5132 p P)). Qed.
Lemma lem50371 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term172 _5131 _5132 p P) = (term166 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50370 _5131 _5132 p P) (@lem50369 _5131 _5132 P)). Qed.
Lemma lem50372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50373 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term177 _5131 _5132 p P) = (term178 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50372) (@lem50371 _5131 _5132 p P)). Qed.
Lemma lem50374 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term174 _5131 _5132 P p1) = (term125 _5131 _5132 P p1).
Proof. exact (eq_refl (term174 _5131 _5132 P p1)). Qed.
Lemma lem50375 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term164 _5131 _5132 p P) = (term164 _5131 _5132 p P).
Proof. exact (eq_refl (term164 _5131 _5132 p P)). Qed.
Lemma lem50376 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : (term179 _5131 _5132 p P p1) = (term180 _5131 _5132 p P p1).
Proof. exact (MK_COMB (@lem50375 _5131 _5132 p P) (@lem50374 _5131 _5132 P p1)). Qed.
Lemma lem50377 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term181 _5131 _5132 p P) = (term182 _5131 _5132 p P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50376 _5131 _5132 p P p1)). Qed.
Lemma lem50378 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem50379 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term173 _5131 _5132 p P) = (term183 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50378 _5132) (@lem50377 _5131 _5132 p P)). Qed.
Lemma lem50380 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : ((term172 _5131 _5132 p P) = (term173 _5131 _5132 p P)) = ((term166 _5131 _5132 p P) = (term183 _5131 _5132 p P)).
Proof. exact (MK_COMB (@lem50373 _5131 _5132 p P) (@lem50379 _5131 _5132 p P)). Qed.
Lemma lem50381 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term166 _5131 _5132 p P) = (term183 _5131 _5132 p P).
Proof. exact (EQ_MP (@lem50380 _5131 _5132 p P) (@lem50365 _5131 _5132 p P)). Qed.
Lemma lem50383 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem50384 {_5131 : Type'} (P : Prop) (Q : _5131 -> Prop) : (term170 _5131 P Q) = (term171 _5131 P Q).
Proof. exact (@lem50383 _5131 P Q). Qed.
Lemma lem50385 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : (term184 _5131 _5132 p P p1) = (term185 _5131 _5132 p P p1).
Proof. exact (@lem50384 _5131 (term157 _5131 _5132 p P) (term124 _5131 _5132 P p1)). Qed.
Lemma lem50386 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term186 _5131 _5132 P p1 p2) = (term122 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term186 _5131 _5132 P p1 p2)). Qed.
Lemma lem50387 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term187 _5131 _5132 P p1) = (term124 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50386 _5131 _5132 P p1 p2)). Qed.
Lemma lem50388 {_5131 : Type'} : (@ex _5131) = (@ex _5131).
Proof. exact (eq_refl (@ex _5131)). Qed.
Lemma lem50389 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term188 _5131 _5132 P p1) = (term125 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50388 _5131) (@lem50387 _5131 _5132 P p1)). Qed.
Lemma lem50390 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term164 _5131 _5132 p P) = (term164 _5131 _5132 p P).
Proof. exact (eq_refl (term164 _5131 _5132 p P)). Qed.
Lemma lem50391 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : (term184 _5131 _5132 p P p1) = (term180 _5131 _5132 p P p1).
Proof. exact (MK_COMB (@lem50390 _5131 _5132 p P) (@lem50389 _5131 _5132 P p1)). Qed.
Lemma lem50392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50393 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : (term189 _5131 _5132 p P p1) = (term190 _5131 _5132 p P p1).
Proof. exact (MK_COMB (@lem50392) (@lem50391 _5131 _5132 p P p1)). Qed.
Lemma lem50394 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term186 _5131 _5132 P p1 p2) = (term122 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term186 _5131 _5132 P p1 p2)). Qed.
Lemma lem50395 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term164 _5131 _5132 p P) = (term164 _5131 _5132 p P).
Proof. exact (eq_refl (term164 _5131 _5132 p P)). Qed.
Lemma lem50396 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term191 _5131 _5132 p P p1 p2) = (term192 _5131 _5132 p P p1 p2).
Proof. exact (MK_COMB (@lem50395 _5131 _5132 p P) (@lem50394 _5131 _5132 P p1 p2)). Qed.
Lemma lem50397 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : (term193 _5131 _5132 p P p1) = (term194 _5131 _5132 p P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50396 _5131 _5132 p P p1 p2)). Qed.
Lemma lem50398 {_5131 : Type'} : (@ex _5131) = (@ex _5131).
Proof. exact (eq_refl (@ex _5131)). Qed.
Lemma lem50399 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : (term185 _5131 _5132 p P p1) = (term195 _5131 _5132 p P p1).
Proof. exact (MK_COMB (@lem50398 _5131) (@lem50397 _5131 _5132 p P p1)). Qed.
Lemma lem50400 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : ((term184 _5131 _5132 p P p1) = (term185 _5131 _5132 p P p1)) = ((term180 _5131 _5132 p P p1) = (term195 _5131 _5132 p P p1)).
Proof. exact (MK_COMB (@lem50393 _5131 _5132 p P p1) (@lem50399 _5131 _5132 p P p1)). Qed.
Lemma lem50401 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) : (term180 _5131 _5132 p P p1) = (term195 _5131 _5132 p P p1).
Proof. exact (EQ_MP (@lem50400 _5131 _5132 p P p1) (@lem50385 _5131 _5132 p P p1)). Qed.
Lemma lem50402 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term182 _5131 _5132 p P) = (term196 _5131 _5132 p P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50401 _5131 _5132 p P p1)). Qed.
Lemma lem50403 {_5132 : Type'} : (@ex _5132) = (@ex _5132).
Proof. exact (eq_refl (@ex _5132)). Qed.
Lemma lem50404 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term183 _5131 _5132 p P) = (term197 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50403 _5132) (@lem50402 _5131 _5132 p P)). Qed.
Lemma lem50405 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term166 _5131 _5132 p P) = (term197 _5131 _5132 p P).
Proof. exact (TRANS (@lem50381 _5131 _5132 p P) (@lem50404 _5131 _5132 p P)). Qed.
Lemma lem50406 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term168 _5131 _5132 P) = (term198 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem50405 _5131 _5132 p P)). Qed.
Lemma lem50407 {_5131 _5132 : Type'} : (@ex (prod _5132 _5131)) = (@ex (prod _5132 _5131)).
Proof. exact (eq_refl (@ex (prod _5132 _5131))). Qed.
Lemma lem50408 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term169 _5131 _5132 P) = (term199 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50407 _5131 _5132) (@lem50406 _5131 _5132 P)). Qed.
Lemma lem50409 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term145 _5131 _5132 P) = (term199 _5131 _5132 P).
Proof. exact (TRANS (@lem50361 _5131 _5132 P) (@lem50408 _5131 _5132 P)). Qed.
Lemma lem50410 {_5131 _5132 : Type'} : (term147 _5131 _5132) = (term200 _5131 _5132).
Proof. exact (fun_ext (fun P : type1223 _5131 _5132 => @lem50409 _5131 _5132 P)). Qed.
Lemma lem50411 {_5131 _5132 : Type'} : (@ex ((prod _5132 _5131) -> Prop)) = (@ex ((prod _5132 _5131) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5132 _5131) -> Prop))). Qed.
Lemma lem50412 {_5131 _5132 : Type'} : (term148 _5131 _5132) = (term201 _5131 _5132).
Proof. exact (MK_COMB (@lem50411 _5131 _5132) (@lem50410 _5131 _5132)). Qed.
Lemma lem50413 {_5131 _5132 : Type'} : (term130 _5131 _5132) = (term201 _5131 _5132).
Proof. exact (TRANS (@lem50335 _5131 _5132) (@lem50412 _5131 _5132)). Qed.
Lemma lem50414 {_5131 _5132 : Type'} : (term93 _5131 _5132) = (term201 _5131 _5132).
Proof. exact (TRANS (@lem50308 _5131 _5132) (@lem50413 _5131 _5132)). Qed.
Lemma lem50415 {_5131 _5132 : Type'} : (term69 _5131 _5132) = (term201 _5131 _5132).
Proof. exact (TRANS (@lem50131 _5131 _5132) (@lem50414 _5131 _5132)). Qed.
Lemma lem50416 {_5131 _5132 : Type'} : (term3 _5131 _5132) = (term201 _5131 _5132).
Proof. exact (TRANS (@lem50104 _5131 _5132) (@lem50415 _5131 _5132)). Qed.
Lemma lem50417 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : term201 _5131 _5132.
Proof. exact (EQ_MP (@lem50416 _5131 _5132) (@lem50039 _5131 _5132 h1)). Qed.
Lemma lem50418 {_5131 _5132 : Type'} (x : prod _5132 _5131) : ((term13 _5131 _5132 x) = x) = ((term13 _5131 _5132 x) = x).
Proof. exact (eq_refl ((term13 _5131 _5132 x) = x)). Qed.
Lemma lem50419 {_5131 _5132 : Type'} : (term14 _5131 _5132) = (term14 _5131 _5132).
Proof. exact (fun_ext (fun x : prod _5132 _5131 => @lem50418 _5131 _5132 x)). Qed.
Lemma lem50420 {_5131 _5132 : Type'} : (@all (prod _5132 _5131)) = (@all (prod _5132 _5131)).
Proof. exact (eq_refl (@all (prod _5132 _5131))). Qed.
Lemma lem50429 {_5131 _5132 : Type'} : (term4 _5131 _5132) = (term4 _5131 _5132).
Proof. exact (MK_COMB (@lem50420 _5131 _5132) (@lem50419 _5131 _5132)). Qed.
Lemma lem50430 {_5131 _5132 : Type'} (h1 : term4 _5131 _5132) : term4 _5131 _5132.
Proof. exact (EQ_MP (@lem50429 _5131 _5132) (@lem50040 _5131 _5132 h1)). Qed.
Lemma lem50431 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (h1 : term199 _5131 _5132 P) : term199 _5131 _5132 P.
Proof. exact (h1). Qed.
Lemma lem50432 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term197 _5131 _5132 p P) : term197 _5131 _5132 p P.
Proof. exact (h1). Qed.
Lemma lem50433 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (h1 : term195 _5131 _5132 p P p1) : term195 _5131 _5132 p P p1.
Proof. exact (h1). Qed.
Lemma lem50434 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term192 _5131 _5132 p P p1 p2) : term192 _5131 _5132 p P p1 p2.
Proof. exact (h1). Qed.
Lemma lem50447 {_5131 _5132 : Type'} (x : prod _5132 _5131) : ((term13 _5131 _5132 x) = x) = ((term13 _5131 _5132 x) = x).
Proof. exact (eq_refl ((term13 _5131 _5132 x) = x)). Qed.
Lemma lem50448 {_5131 _5132 : Type'} : (term14 _5131 _5132) = (term14 _5131 _5132).
Proof. exact (fun_ext (fun x : prod _5132 _5131 => @lem50447 _5131 _5132 x)). Qed.
Lemma lem50449 {_5131 _5132 : Type'} : (@all (prod _5132 _5131)) = (@all (prod _5132 _5131)).
Proof. exact (eq_refl (@all (prod _5132 _5131))). Qed.
Lemma lem50450 {_5131 _5132 : Type'} : (term4 _5131 _5132) = (term4 _5131 _5132).
Proof. exact (MK_COMB (@lem50449 _5131 _5132) (@lem50448 _5131 _5132)). Qed.
Lemma lem50451 {_5131 _5132 : Type'} (h1 : term4 _5131 _5132) : term4 _5131 _5132.
Proof. exact (EQ_MP (@lem50450 _5131 _5132) (@lem50430 _5131 _5132 h1)). Qed.
Lemma lem50458 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term15 _5131 _5132 P p1 p2) = (term15 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term15 _5131 _5132 P p1 p2)). Qed.
Lemma lem50463 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (term30 _5131 _5132 P p) = (term30 _5131 _5132 P p).
Proof. exact (eq_refl (term30 _5131 _5132 P p)). Qed.
Lemma lem50464 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term32 _5131 _5132 P) = (term32 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem50463 _5131 _5132 P p)). Qed.
Lemma lem50465 {_5131 _5132 : Type'} : (@all (prod _5132 _5131)) = (@all (prod _5132 _5131)).
Proof. exact (eq_refl (@all (prod _5132 _5131))). Qed.
Lemma lem50466 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term25 _5131 _5132 P) = (term25 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50465 _5131 _5132) (@lem50464 _5131 _5132 P)). Qed.
Lemma lem50467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem50468 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term51 _5131 _5132 P) = (term51 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50467) (@lem50466 _5131 _5132 P)). Qed.
Lemma lem50469 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term122 _5131 _5132 P p1 p2) = (term122 _5131 _5132 P p1 p2).
Proof. exact (MK_COMB (@lem50468 _5131 _5132 P) (@lem50458 _5131 _5132 P p1 p2)). Qed.
Lemma lem50478 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term39 _5131 _5132 P p1 p2) = (term39 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term39 _5131 _5132 P p1 p2)). Qed.
Lemma lem50479 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term41 _5131 _5132 P p1) = (term41 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50478 _5131 _5132 P p1 p2)). Qed.
Lemma lem50480 {_5131 : Type'} : (@all _5131) = (@all _5131).
Proof. exact (eq_refl (@all _5131)). Qed.
Lemma lem50481 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term42 _5131 _5132 P p1) = (term42 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50480 _5131) (@lem50479 _5131 _5132 P p1)). Qed.
Lemma lem50482 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term48 _5131 _5132 P) = (term48 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50481 _5131 _5132 P p1)). Qed.
Lemma lem50483 {_5132 : Type'} : (@all _5132) = (@all _5132).
Proof. exact (eq_refl (@all _5132)). Qed.
Lemma lem50484 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term49 _5131 _5132 P) = (term49 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50483 _5132) (@lem50482 _5131 _5132 P)). Qed.
Lemma lem50489 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (term202 _5131 _5132 P p) = (term202 _5131 _5132 P p).
Proof. exact (eq_refl (term202 _5131 _5132 P p)). Qed.
Lemma lem50490 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term157 _5131 _5132 p P) = (term157 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50489 _5131 _5132 P p) (@lem50484 _5131 _5132 P)). Qed.
Lemma lem50491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem50492 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) : (term164 _5131 _5132 p P) = (term164 _5131 _5132 p P).
Proof. exact (MK_COMB (@lem50491) (@lem50490 _5131 _5132 p P)). Qed.
Lemma lem50493 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term192 _5131 _5132 p P p1 p2) = (term192 _5131 _5132 p P p1 p2).
Proof. exact (MK_COMB (@lem50492 _5131 _5132 p P) (@lem50469 _5131 _5132 P p1 p2)). Qed.
Lemma lem50494 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term192 _5131 _5132 p P p1 p2) : term192 _5131 _5132 p P p1 p2.
Proof. exact (EQ_MP (@lem50493 _5131 _5132 p P p1 p2) (@lem50434 _5131 _5132 p P p1 p2 h1)). Qed.
Lemma lem50495 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term157 _5131 _5132 p P.
Proof. exact (h1). Qed.
Lemma lem50496 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term122 _5131 _5132 P p1 p2.
Proof. exact (h1). Qed.
Lemma lem50497 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term49 _5131 _5132 P.
Proof. exact (proj2 (@lem50495 _5131 _5132 p P h1)). Qed.
Lemma lem50500 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term25 _5131 _5132 P.
Proof. exact (proj1 (@lem50496 _5131 _5132 P p1 p2 h1)). Qed.
Lemma lem50502 {_5131 _5132 : Type'} (x : prod _5132 _5131) : ((term13 _5131 _5132 x) = x) = ((term13 _5131 _5132 x) = x).
Proof. exact (eq_refl ((term13 _5131 _5132 x) = x)). Qed.
Lemma lem50503 {_5131 _5132 : Type'} : (term14 _5131 _5132) = (term14 _5131 _5132).
Proof. exact (fun_ext (fun x : prod _5132 _5131 => @lem50502 _5131 _5132 x)). Qed.
Lemma lem50504 {_5131 _5132 : Type'} : (@all (prod _5132 _5131)) = (@all (prod _5132 _5131)).
Proof. exact (eq_refl (@all (prod _5132 _5131))). Qed.
Lemma lem50506 {_5131 _5132 : Type'} : (term4 _5131 _5132) = (term4 _5131 _5132).
Proof. exact (MK_COMB (@lem50504 _5131 _5132) (@lem50503 _5131 _5132)). Qed.
Lemma lem50507 {_5131 _5132 : Type'} (h1 : term4 _5131 _5132) : term4 _5131 _5132.
Proof. exact (EQ_MP (@lem50506 _5131 _5132) (@lem50451 _5131 _5132 h1)). Qed.
Lemma lem50513 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term39 _5131 _5132 P p1 p2) = (term39 _5131 _5132 P p1 p2).
Proof. exact (eq_refl (term39 _5131 _5132 P p1 p2)). Qed.
Lemma lem50514 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term41 _5131 _5132 P p1) = (term41 _5131 _5132 P p1).
Proof. exact (fun_ext (fun p2 : _5131 => @lem50513 _5131 _5132 P p1 p2)). Qed.
Lemma lem50515 {_5131 : Type'} : (@all _5131) = (@all _5131).
Proof. exact (eq_refl (@all _5131)). Qed.
Lemma lem50516 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) : (term42 _5131 _5132 P p1) = (term42 _5131 _5132 P p1).
Proof. exact (MK_COMB (@lem50515 _5131) (@lem50514 _5131 _5132 P p1)). Qed.
Lemma lem50517 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term48 _5131 _5132 P) = (term48 _5131 _5132 P).
Proof. exact (fun_ext (fun p1 : _5132 => @lem50516 _5131 _5132 P p1)). Qed.
Lemma lem50518 {_5132 : Type'} : (@all _5132) = (@all _5132).
Proof. exact (eq_refl (@all _5132)). Qed.
Lemma lem50520 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term49 _5131 _5132 P) = (term49 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50518 _5132) (@lem50517 _5131 _5132 P)). Qed.
Lemma lem50521 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term49 _5131 _5132 P.
Proof. exact (EQ_MP (@lem50520 _5131 _5132 P) (@lem50497 _5131 _5132 p P h1)). Qed.
Lemma lem50530 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (term30 _5131 _5132 P p) = (term30 _5131 _5132 P p).
Proof. exact (eq_refl (term30 _5131 _5132 P p)). Qed.
Lemma lem50531 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term32 _5131 _5132 P) = (term32 _5131 _5132 P).
Proof. exact (fun_ext (fun p : prod _5132 _5131 => @lem50530 _5131 _5132 P p)). Qed.
Lemma lem50532 {_5131 _5132 : Type'} : (@all (prod _5132 _5131)) = (@all (prod _5132 _5131)).
Proof. exact (eq_refl (@all (prod _5132 _5131))). Qed.
Lemma lem50534 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term25 _5131 _5132 P) = (term25 _5131 _5132 P).
Proof. exact (MK_COMB (@lem50532 _5131 _5132) (@lem50531 _5131 _5132 P)). Qed.
Lemma lem50535 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term25 _5131 _5132 P.
Proof. exact (EQ_MP (@lem50534 _5131 _5132 P) (@lem50500 _5131 _5132 P p1 p2 h1)). Qed.
Lemma lem50540 {_5131 _5132 : Type'} (_1368 : prod _5132 _5131) (h1 : term4 _5131 _5132) : term203 _5131 _5132 _1368.
Proof. exact (@lem50507 _5131 _5132 h1 _1368). Qed.
Lemma lem50541 {_5131 _5132 : Type'} (_1368 : prod _5132 _5131) : (term203 _5131 _5132 _1368) = ((term13 _5131 _5132 _1368) = _1368).
Proof. exact (eq_refl (term203 _5131 _5132 _1368)). Qed.
Lemma lem50543 {_5131 _5132 : Type'} (_1369 : _5132) (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term204 _5131 _5132 P _1369.
Proof. exact (@lem50521 _5131 _5132 p P h1 _1369). Qed.
Lemma lem50544 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1369 : _5132) : (term204 _5131 _5132 P _1369) = (term42 _5131 _5132 P _1369).
Proof. exact (eq_refl (term204 _5131 _5132 P _1369)). Qed.
Lemma lem50545 {_5131 _5132 : Type'} (_1369 : _5132) (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term42 _5131 _5132 P _1369.
Proof. exact (EQ_MP (@lem50544 _5131 _5132 P _1369) (@lem50543 _5131 _5132 _1369 p P h1)). Qed.
Lemma lem50546 {_5131 _5132 : Type'} (_1369 : _5132) (_1370 : _5131) (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term205 _5131 _5132 P _1369 _1370.
Proof. exact (@lem50545 _5131 _5132 _1369 p P h1 _1370). Qed.
Lemma lem50547 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1369 : _5132) (_1370 : _5131) : (term205 _5131 _5132 P _1369 _1370) = (term39 _5131 _5132 P _1369 _1370).
Proof. exact (eq_refl (term205 _5131 _5132 P _1369 _1370)). Qed.
Lemma lem50552 {_5131 _5132 : Type'} (_1372 : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term206 _5131 _5132 P _1372.
Proof. exact (@lem50535 _5131 _5132 P p1 p2 h1 _1372). Qed.
Lemma lem50553 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1372 : prod _5132 _5131) : (term206 _5131 _5132 P _1372) = (term30 _5131 _5132 P _1372).
Proof. exact (eq_refl (term206 _5131 _5132 P _1372)). Qed.
Lemma lem50560 {_5131 _5132 : Type'} (_1369 : _5132) (_1370 : _5131) (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term39 _5131 _5132 P _1369 _1370.
Proof. exact (EQ_MP (@lem50547 _5131 _5132 P _1369 _1370) (@lem50546 _5131 _5132 _1369 _1370 p P h1)). Qed.
Lemma lem50564 {_5131 _5132 : Type'} (_1372 : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term30 _5131 _5132 P _1372.
Proof. exact (EQ_MP (@lem50553 _5131 _5132 P _1372) (@lem50552 _5131 _5132 _1372 P p1 p2 h1)). Qed.
Lemma lem50567 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem50568 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) (h1 : _1373 = _1374) : _1373 = _1374.
Proof. exact (h1). Qed.
Lemma lem50569 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) (h1 : _1373 = _1374) : (P _1373) = (P _1374).
Proof. exact (MK_COMB (@lem50567 _5131 _5132 P) (@lem50568 _5131 _5132 _1373 _1374 h1)). Qed.
Lemma lem50571 (b : Prop) (a : Prop) : term207 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem50572 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : term208 _5131 _5132 _1374 P _1373.
Proof. exact (@lem50571 (P _1374) (P _1373)). Qed.
Lemma lem50573 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) (h1 : _1373 = _1374) : term209 _5131 _5132 _1374 P _1373.
Proof. exact (@lem50572 _5131 _5132 _1374 P _1373 (@lem50569 _5131 _5132 P _1373 _1374 h1)). Qed.
Lemma lem50574 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : term210 _5131 _5132 _1374 P _1373.
Proof. exact (fun h0 : _1373 = _1374 => @lem50573 _5131 _5132 P _1373 _1374 h0). Qed.
Lemma lem50576 (a : Prop) (b : Prop) : (a -> b) = (term211 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem50577 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term210 _5131 _5132 _1374 P _1373) = (term212 _5131 _5132 _1374 P _1373).
Proof. exact (@lem50576 (_1373 = _1374) (term209 _5131 _5132 _1374 P _1373)). Qed.
Lemma lem50578 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : term212 _5131 _5132 _1374 P _1373.
Proof. exact (EQ_MP (@lem50577 _5131 _5132 _1374 P _1373) (@lem50574 _5131 _5132 _1374 P _1373)). Qed.
Lemma lem50611 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) (z : prod _5132 _5131) : term213 _5131 _5132 x y z.
Proof. exact (@lem21385 (prod _5132 _5131) x y z). Qed.
Lemma lem50617 {_5131 _5132 : Type'} (_1368 : prod _5132 _5131) (h1 : term4 _5131 _5132) : (term13 _5131 _5132 _1368) = _1368.
Proof. exact (EQ_MP (@lem50541 _5131 _5132 _1368) (@lem50540 _5131 _5132 _1368 h1)). Qed.
Lemma lem50618 {_5131 _5132 : Type'} (_1368 : prod _5132 _5131) (h1 : term4 _5131 _5132) : (term13 _5131 _5132 _1368) = _1368.
Proof. exact (@lem50617 _5131 _5132 _1368 h1). Qed.
Lemma lem50619 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : (term13 _5131 _5132 p) = p.
Proof. exact (@lem50618 _5131 _5132 p h1). Qed.
Lemma lem50620 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : term214 _5131 _5132 p.
Proof. exact (fun h0 : term215 _5131 _5132 p => @lem50619 _5131 _5132 p h1). Qed.
Lemma lem50622 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50623 {_5131 _5132 : Type'} (p : prod _5132 _5131) : (term214 _5131 _5132 p) = ((term13 _5131 _5132 p) = p).
Proof. exact (@lem50622 ((term13 _5131 _5132 p) = p)). Qed.
Lemma lem50624 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : (term13 _5131 _5132 p) = p.
Proof. exact (EQ_MP (@lem50623 _5131 _5132 p) (@lem50620 _5131 _5132 p h1)). Qed.
Lemma lem50626 {_5131 _5132 : Type'} (x : prod _5132 _5131) : x = x.
Proof. exact (@lem21386 (prod _5132 _5131) x). Qed.
Lemma lem50627 {_5131 _5132 : Type'} (x : prod _5132 _5131) : x = x.
Proof. exact (@lem50626 _5131 _5132 x). Qed.
Lemma lem50628 {_5131 _5132 : Type'} (p : prod _5132 _5131) : (term13 _5131 _5132 p) = (term13 _5131 _5132 p).
Proof. exact (@lem50627 _5131 _5132 (term13 _5131 _5132 p)). Qed.
Lemma lem50629 {_5131 _5132 : Type'} (p : prod _5132 _5131) : term217 _5131 _5132 p.
Proof. exact (fun h0 : term218 _5131 _5132 p => @lem50628 _5131 _5132 p). Qed.
Lemma lem50631 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50632 {_5131 _5132 : Type'} (p : prod _5132 _5131) : (term217 _5131 _5132 p) = ((term13 _5131 _5132 p) = (term13 _5131 _5132 p)).
Proof. exact (@lem50631 ((term13 _5131 _5132 p) = (term13 _5131 _5132 p))). Qed.
Lemma lem50633 {_5131 _5132 : Type'} (p : prod _5132 _5131) : (term13 _5131 _5132 p) = (term13 _5131 _5132 p).
Proof. exact (EQ_MP (@lem50632 _5131 _5132 p) (@lem50629 _5131 _5132 p)). Qed.
Lemma lem50651 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem50652 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term219 _5131 _5132 x y z) = (term220 _5131 _5132 y x z).
Proof. exact (@lem50651 (y = z) (term221 _5131 _5132 x z)). Qed.
Lemma lem50662 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) : (term222 _5131 _5132 x y) = (term222 _5131 _5132 x y).
Proof. exact (eq_refl (term222 _5131 _5132 x y)). Qed.
Lemma lem50663 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term213 _5131 _5132 x y z) = (term223 _5131 _5132 y x z).
Proof. exact (MK_COMB (@lem50662 _5131 _5132 x y) (@lem50652 _5131 _5132 y x z)). Qed.
Lemma lem50667 (q : Prop) (p : Prop) (r : Prop) : (term224 p q r) = (term224 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem50668 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term223 _5131 _5132 y x z) = (term225 _5131 _5132 y x z).
Proof. exact (@lem50667 (y = z) (term221 _5131 _5132 x y) (term221 _5131 _5132 x z)). Qed.
Lemma lem50690 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term213 _5131 _5132 x y z) = (term225 _5131 _5132 y x z).
Proof. exact (TRANS (@lem50663 _5131 _5132 y x z) (@lem50668 _5131 _5132 y x z)). Qed.
Lemma lem50691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50692 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term226 _5131 _5132 x y z) = (term227 _5131 _5132 y x z).
Proof. exact (MK_COMB (@lem50691) (@lem50690 _5131 _5132 y x z)). Qed.
Lemma lem50714 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term225 _5131 _5132 y x z) = (term225 _5131 _5132 y x z).
Proof. exact (eq_refl (term225 _5131 _5132 y x z)). Qed.
Lemma lem50715 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : ((term213 _5131 _5132 x y z) = (term225 _5131 _5132 y x z)) = ((term225 _5131 _5132 y x z) = (term225 _5131 _5132 y x z)).
Proof. exact (MK_COMB (@lem50692 _5131 _5132 y x z) (@lem50714 _5131 _5132 y x z)). Qed.
Lemma lem50717 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem50718 (x : Prop) : (x = x) = True.
Proof. exact (@lem50717 Prop x). Qed.
Lemma lem50719 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : ((term225 _5131 _5132 y x z) = (term225 _5131 _5132 y x z)) = True.
Proof. exact (@lem50718 (term225 _5131 _5132 y x z)). Qed.
Lemma lem50720 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : ((term213 _5131 _5132 x y z) = (term225 _5131 _5132 y x z)) = True.
Proof. exact (TRANS (@lem50715 _5131 _5132 y x z) (@lem50719 _5131 _5132 y x z)). Qed.
Lemma lem50721 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : True = ((term213 _5131 _5132 x y z) = (term225 _5131 _5132 y x z)).
Proof. exact (SYM (@lem50720 _5131 _5132 y x z)). Qed.
Lemma lem50722 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term213 _5131 _5132 x y z) = (term225 _5131 _5132 y x z).
Proof. exact (EQ_MP (@lem50721 _5131 _5132 y x z) (@lem0)). Qed.
Lemma lem50723 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : term225 _5131 _5132 y x z.
Proof. exact (EQ_MP (@lem50722 _5131 _5132 y x z) (@lem50611 _5131 _5132 x y z)). Qed.
Lemma lem50725 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem50726 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) (z : prod _5132 _5131) : (term225 _5131 _5132 y x z) = (term229 _5131 _5132 x y z).
Proof. exact (@lem50725 (term230 _5131 _5132 y x z) (y = z)). Qed.
Lemma lem50728 (a : Prop) (b : Prop) : (term231 a b) = (term232 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem50729 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term233 _5131 _5132 y x z) = (term234 _5131 _5132 y x z).
Proof. exact (@lem50728 (term221 _5131 _5132 x y) (term221 _5131 _5132 x z)). Qed.
Lemma lem50731 (a : Prop) : (term235 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem50732 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) : (term236 _5131 _5132 x y) = (x = y).
Proof. exact (@lem50731 (x = y)). Qed.
Lemma lem50733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem50734 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) : (term237 _5131 _5132 x y) = (term238 _5131 _5132 x y).
Proof. exact (MK_COMB (@lem50733) (@lem50732 _5131 _5132 x y)). Qed.
Lemma lem50736 (a : Prop) : (term235 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem50737 {_5131 _5132 : Type'} (x : prod _5132 _5131) (z : prod _5132 _5131) : (term236 _5131 _5132 x z) = (x = z).
Proof. exact (@lem50736 (x = z)). Qed.
Lemma lem50738 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term234 _5131 _5132 y x z) = (term239 _5131 _5132 y x z).
Proof. exact (MK_COMB (@lem50734 _5131 _5132 x y) (@lem50737 _5131 _5132 x z)). Qed.
Lemma lem50739 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term233 _5131 _5132 y x z) = (term239 _5131 _5132 y x z).
Proof. exact (TRANS (@lem50729 _5131 _5132 y x z) (@lem50738 _5131 _5132 y x z)). Qed.
Lemma lem50740 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem50741 {_5131 _5132 : Type'} (y : prod _5132 _5131) (x : prod _5132 _5131) (z : prod _5132 _5131) : (term240 _5131 _5132 y x z) = (term241 _5131 _5132 y x z).
Proof. exact (MK_COMB (@lem50740) (@lem50739 _5131 _5132 y x z)). Qed.
Lemma lem50742 {_5131 _5132 : Type'} (y : prod _5132 _5131) (z : prod _5132 _5131) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem50743 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) (z : prod _5132 _5131) : (term229 _5131 _5132 x y z) = (term242 _5131 _5132 x y z).
Proof. exact (MK_COMB (@lem50741 _5131 _5132 y x z) (@lem50742 _5131 _5132 y z)). Qed.
Lemma lem50744 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) (z : prod _5132 _5131) : (term225 _5131 _5132 y x z) = (term242 _5131 _5132 x y z).
Proof. exact (TRANS (@lem50726 _5131 _5132 x y z) (@lem50743 _5131 _5132 x y z)). Qed.
Lemma lem50746 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : term243 _5131 _5132 p.
Proof. exact (conj (@lem50624 _5131 _5132 p h1) (@lem50633 _5131 _5132 p)). Qed.
Lemma lem50748 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) (z : prod _5132 _5131) : term242 _5131 _5132 x y z.
Proof. exact (EQ_MP (@lem50744 _5131 _5132 x y z) (@lem50723 _5131 _5132 y x z)). Qed.
Lemma lem50749 {_5131 _5132 : Type'} (x : prod _5132 _5131) (y : prod _5132 _5131) (z : prod _5132 _5131) : term242 _5131 _5132 x y z.
Proof. exact (@lem50748 _5131 _5132 x y z). Qed.
Lemma lem50750 {_5131 _5132 : Type'} (p : prod _5132 _5131) : term244 _5131 _5132 p.
Proof. exact (@lem50749 _5131 _5132 (term13 _5131 _5132 p) p (term13 _5131 _5132 p)). Qed.
Lemma lem50753 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : p = (term13 _5131 _5132 p).
Proof. exact (@lem50750 _5131 _5132 p (@lem50746 _5131 _5132 p h1)). Qed.
Lemma lem50754 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : p = (term13 _5131 _5132 p).
Proof. exact (@lem50753 _5131 _5132 p h1). Qed.
Lemma lem50755 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : term245 _5131 _5132 p.
Proof. exact (fun h0 : term246 _5131 _5132 p => @lem50754 _5131 _5132 p h1). Qed.
Lemma lem50757 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50758 {_5131 _5132 : Type'} (p : prod _5132 _5131) : (term245 _5131 _5132 p) = (p = (term13 _5131 _5132 p)).
Proof. exact (@lem50757 (p = (term13 _5131 _5132 p))). Qed.
Lemma lem50759 {_5131 _5132 : Type'} (p : prod _5132 _5131) (h1 : term4 _5131 _5132) : p = (term13 _5131 _5132 p).
Proof. exact (EQ_MP (@lem50758 _5131 _5132 p) (@lem50755 _5131 _5132 p h1)). Qed.
Lemma lem50761 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : P p.
Proof. exact (proj1 (@lem50495 _5131 _5132 p P h1)). Qed.
Lemma lem50762 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term247 _5131 _5132 P p.
Proof. exact (fun h0 : term30 _5131 _5132 P p => @lem50761 _5131 _5132 p P h1). Qed.
Lemma lem50764 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50765 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (term247 _5131 _5132 P p) = (P p).
Proof. exact (@lem50764 (P p)). Qed.
Lemma lem50766 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : P p.
Proof. exact (EQ_MP (@lem50765 _5131 _5132 P p) (@lem50762 _5131 _5132 p P h1)). Qed.
Lemma lem50772 (q : Prop) (p : Prop) (r : Prop) : (term224 p q r) = (term224 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem50773 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term212 _5131 _5132 _1374 P _1373) = (term248 _5131 _5132 _1374 P _1373).
Proof. exact (@lem50772 (P _1374) (term221 _5131 _5132 _1373 _1374) (term30 _5131 _5132 P _1373)). Qed.
Lemma lem50787 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem50788 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term249 _5131 _5132 _1374 P _1373) = (term250 _5131 _5132 P _1373 _1374).
Proof. exact (@lem50787 (term30 _5131 _5132 P _1373) (term221 _5131 _5132 _1373 _1374)). Qed.
Lemma lem50796 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : (term251 _5131 _5132 P _1374) = (term251 _5131 _5132 P _1374).
Proof. exact (eq_refl (term251 _5131 _5132 P _1374)). Qed.
Lemma lem50797 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term248 _5131 _5132 _1374 P _1373) = (term252 _5131 _5132 P _1373 _1374).
Proof. exact (MK_COMB (@lem50796 _5131 _5132 P _1374) (@lem50788 _5131 _5132 P _1373 _1374)). Qed.
Lemma lem50808 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term212 _5131 _5132 _1374 P _1373) = (term252 _5131 _5132 P _1373 _1374).
Proof. exact (TRANS (@lem50773 _5131 _5132 _1374 P _1373) (@lem50797 _5131 _5132 P _1373 _1374)). Qed.
Lemma lem50809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem50810 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term253 _5131 _5132 _1374 P _1373) = (term254 _5131 _5132 P _1373 _1374).
Proof. exact (MK_COMB (@lem50809) (@lem50808 _5131 _5132 P _1373 _1374)). Qed.
Lemma lem50824 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem50825 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term249 _5131 _5132 _1374 P _1373) = (term250 _5131 _5132 P _1373 _1374).
Proof. exact (@lem50824 (term30 _5131 _5132 P _1373) (term221 _5131 _5132 _1373 _1374)). Qed.
Lemma lem50833 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : (term251 _5131 _5132 P _1374) = (term251 _5131 _5132 P _1374).
Proof. exact (eq_refl (term251 _5131 _5132 P _1374)). Qed.
Lemma lem50834 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term248 _5131 _5132 _1374 P _1373) = (term252 _5131 _5132 P _1373 _1374).
Proof. exact (MK_COMB (@lem50833 _5131 _5132 P _1374) (@lem50825 _5131 _5132 P _1373 _1374)). Qed.
Lemma lem50845 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : ((term212 _5131 _5132 _1374 P _1373) = (term248 _5131 _5132 _1374 P _1373)) = ((term252 _5131 _5132 P _1373 _1374) = (term252 _5131 _5132 P _1373 _1374)).
Proof. exact (MK_COMB (@lem50810 _5131 _5132 P _1373 _1374) (@lem50834 _5131 _5132 P _1373 _1374)). Qed.
Lemma lem50847 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem50848 (x : Prop) : (x = x) = True.
Proof. exact (@lem50847 Prop x). Qed.
Lemma lem50849 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : ((term252 _5131 _5132 P _1373 _1374) = (term252 _5131 _5132 P _1373 _1374)) = True.
Proof. exact (@lem50848 (term252 _5131 _5132 P _1373 _1374)). Qed.
Lemma lem50850 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : ((term212 _5131 _5132 _1374 P _1373) = (term248 _5131 _5132 _1374 P _1373)) = True.
Proof. exact (TRANS (@lem50845 _5131 _5132 P _1373 _1374) (@lem50849 _5131 _5132 P _1373 _1374)). Qed.
Lemma lem50851 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : True = ((term212 _5131 _5132 _1374 P _1373) = (term248 _5131 _5132 _1374 P _1373)).
Proof. exact (SYM (@lem50850 _5131 _5132 _1374 P _1373)). Qed.
Lemma lem50852 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term212 _5131 _5132 _1374 P _1373) = (term248 _5131 _5132 _1374 P _1373).
Proof. exact (EQ_MP (@lem50851 _5131 _5132 _1374 P _1373) (@lem0)). Qed.
Lemma lem50853 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : term248 _5131 _5132 _1374 P _1373.
Proof. exact (EQ_MP (@lem50852 _5131 _5132 _1374 P _1373) (@lem50578 _5131 _5132 _1374 P _1373)). Qed.
Lemma lem50855 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem50856 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : (term248 _5131 _5132 _1374 P _1373) = (term255 _5131 _5132 _1373 P _1374).
Proof. exact (@lem50855 (term249 _5131 _5132 _1374 P _1373) (P _1374)). Qed.
Lemma lem50858 (a : Prop) (b : Prop) : (term231 a b) = (term232 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem50859 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term256 _5131 _5132 _1374 P _1373) = (term257 _5131 _5132 _1374 P _1373).
Proof. exact (@lem50858 (term221 _5131 _5132 _1373 _1374) (term30 _5131 _5132 P _1373)). Qed.
Lemma lem50861 (a : Prop) : (term235 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem50862 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term236 _5131 _5132 _1373 _1374) = (_1373 = _1374).
Proof. exact (@lem50861 (_1373 = _1374)). Qed.
Lemma lem50863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem50864 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (_1374 : prod _5132 _5131) : (term237 _5131 _5132 _1373 _1374) = (term238 _5131 _5132 _1373 _1374).
Proof. exact (MK_COMB (@lem50863) (@lem50862 _5131 _5132 _1373 _1374)). Qed.
Lemma lem50866 (a : Prop) : (term235 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem50867 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term258 _5131 _5132 P _1373) = (P _1373).
Proof. exact (@lem50866 (P _1373)). Qed.
Lemma lem50868 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term257 _5131 _5132 _1374 P _1373) = (term259 _5131 _5132 _1374 P _1373).
Proof. exact (MK_COMB (@lem50864 _5131 _5132 _1373 _1374) (@lem50867 _5131 _5132 P _1373)). Qed.
Lemma lem50869 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term256 _5131 _5132 _1374 P _1373) = (term259 _5131 _5132 _1374 P _1373).
Proof. exact (TRANS (@lem50859 _5131 _5132 _1374 P _1373) (@lem50868 _5131 _5132 _1374 P _1373)). Qed.
Lemma lem50870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem50871 {_5131 _5132 : Type'} (_1374 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1373 : prod _5132 _5131) : (term260 _5131 _5132 _1374 P _1373) = (term261 _5131 _5132 _1374 P _1373).
Proof. exact (MK_COMB (@lem50870) (@lem50869 _5131 _5132 _1374 P _1373)). Qed.
Lemma lem50872 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : (P _1374) = (P _1374).
Proof. exact (eq_refl (P _1374)). Qed.
Lemma lem50873 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : (term255 _5131 _5132 _1373 P _1374) = (term262 _5131 _5132 _1373 P _1374).
Proof. exact (MK_COMB (@lem50871 _5131 _5132 _1374 P _1373) (@lem50872 _5131 _5132 P _1374)). Qed.
Lemma lem50874 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : (term248 _5131 _5132 _1374 P _1373) = (term262 _5131 _5132 _1373 P _1374).
Proof. exact (TRANS (@lem50856 _5131 _5132 _1373 P _1374) (@lem50873 _5131 _5132 _1373 P _1374)). Qed.
Lemma lem50876 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : term263 _5131 _5132 P p.
Proof. exact (conj (@lem50759 _5131 _5132 p h1) (@lem50766 _5131 _5132 p P h2)). Qed.
Lemma lem50878 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : term262 _5131 _5132 _1373 P _1374.
Proof. exact (EQ_MP (@lem50874 _5131 _5132 _1373 P _1374) (@lem50853 _5131 _5132 _1374 P _1373)). Qed.
Lemma lem50879 {_5131 _5132 : Type'} (_1373 : prod _5132 _5131) (P : type1223 _5131 _5132) (_1374 : prod _5132 _5131) : term262 _5131 _5132 _1373 P _1374.
Proof. exact (@lem50878 _5131 _5132 _1373 P _1374). Qed.
Lemma lem50880 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : term264 _5131 _5132 P p.
Proof. exact (@lem50879 _5131 _5132 p P (term13 _5131 _5132 p)). Qed.
Lemma lem50883 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : term265 _5131 _5132 P p.
Proof. exact (@lem50880 _5131 _5132 P p (@lem50876 _5131 _5132 p P h1 h2)). Qed.
Lemma lem50884 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : term266 _5131 _5132 P p.
Proof. exact (fun h0 : term267 _5131 _5132 P p => @lem50883 _5131 _5132 p P h1 h2). Qed.
Lemma lem50886 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50887 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p : prod _5132 _5131) : (term266 _5131 _5132 P p) = (term265 _5131 _5132 P p).
Proof. exact (@lem50886 (term265 _5131 _5132 P p)). Qed.
Lemma lem50888 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : term265 _5131 _5132 P p.
Proof. exact (EQ_MP (@lem50887 _5131 _5132 P p) (@lem50884 _5131 _5132 p P h1 h2)). Qed.
Lemma lem50891 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem50893 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1369 : _5132) (_1370 : _5131) : (term39 _5131 _5132 P _1369 _1370) = (term268 _5131 _5132 P _1369 _1370).
Proof. exact (@lem50891 (term15 _5131 _5132 P _1369 _1370)). Qed.
Lemma lem50896 {_5131 _5132 : Type'} (_1369 : _5132) (_1370 : _5131) (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term268 _5131 _5132 P _1369 _1370.
Proof. exact (EQ_MP (@lem50893 _5131 _5132 P _1369 _1370) (@lem50560 _5131 _5132 _1369 _1370 p P h1)). Qed.
Lemma lem50897 {_5131 _5132 : Type'} (_1369 : _5132) (_1370 : _5131) (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term268 _5131 _5132 P _1369 _1370.
Proof. exact (@lem50896 _5131 _5132 _1369 _1370 p P h1). Qed.
Lemma lem50898 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term157 _5131 _5132 p P) : term269 _5131 _5132 P p.
Proof. exact (@lem50897 _5131 _5132 (@fst _5132 _5131 p) (@snd _5132 _5131 p) p P h1). Qed.
Lemma lem50901 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : False.
Proof. exact (@lem50898 _5131 _5132 p P h2 (@lem50888 _5131 _5132 p P h1 h2)). Qed.
Lemma lem50902 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : term270.
Proof. exact (fun h0 : ~ False => @lem50901 _5131 _5132 p P h1 h2). Qed.
Lemma lem50904 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50905 : term270 = False.
Proof. exact (@lem50904 False). Qed.
Lemma lem50906 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : False.
Proof. exact (EQ_MP (@lem50905) (@lem50902 _5131 _5132 p P h1 h2)). Qed.
Lemma lem50957 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term15 _5131 _5132 P p1 p2.
Proof. exact (proj2 (@lem50496 _5131 _5132 P p1 p2 h1)). Qed.
Lemma lem50958 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term271 _5131 _5132 P p1 p2.
Proof. exact (fun h0 : term39 _5131 _5132 P p1 p2 => @lem50957 _5131 _5132 P p1 p2 h1). Qed.
Lemma lem50960 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50961 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) : (term271 _5131 _5132 P p1 p2) = (term15 _5131 _5132 P p1 p2).
Proof. exact (@lem50960 (term15 _5131 _5132 P p1 p2)). Qed.
Lemma lem50962 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term15 _5131 _5132 P p1 p2.
Proof. exact (EQ_MP (@lem50961 _5131 _5132 P p1 p2) (@lem50958 _5131 _5132 P p1 p2 h1)). Qed.
Lemma lem50965 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem50967 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (_1372 : prod _5132 _5131) : (term30 _5131 _5132 P _1372) = (term272 _5131 _5132 P _1372).
Proof. exact (@lem50965 (P _1372)). Qed.
Lemma lem50970 {_5131 _5132 : Type'} (_1372 : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term272 _5131 _5132 P _1372.
Proof. exact (EQ_MP (@lem50967 _5131 _5132 P _1372) (@lem50564 _5131 _5132 _1372 P p1 p2 h1)). Qed.
Lemma lem50971 {_5131 _5132 : Type'} (_1372 : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term272 _5131 _5132 P _1372.
Proof. exact (@lem50970 _5131 _5132 _1372 P p1 p2 h1). Qed.
Lemma lem50972 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term268 _5131 _5132 P p1 p2.
Proof. exact (@lem50971 _5131 _5132 (@pair _5132 _5131 p1 p2) P p1 p2 h1). Qed.
Lemma lem50975 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : False.
Proof. exact (@lem50972 _5131 _5132 P p1 p2 h1 (@lem50962 _5131 _5132 P p1 p2 h1)). Qed.
Lemma lem50976 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : term270.
Proof. exact (fun h0 : ~ False => @lem50975 _5131 _5132 P p1 p2 h1). Qed.
Lemma lem50978 (p : Prop) : (term216 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem50979 : term270 = False.
Proof. exact (@lem50978 False). Qed.
Lemma lem50980 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term122 _5131 _5132 P p1 p2) : False.
Proof. exact (EQ_MP (@lem50979) (@lem50976 _5131 _5132 P p1 p2 h1)). Qed.
Lemma lem50981 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : (term4 _5131 _5132) = False.
Proof. exact (prop_ext (fun h3 : term4 _5131 _5132 => @lem50906 _5131 _5132 p P h1 h2) (fun h3 : False => @lem50507 _5131 _5132 h1)). Qed.
Lemma lem50982 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term157 _5131 _5132 p P) : False.
Proof. exact (EQ_MP (@lem50981 _5131 _5132 p P h1 h2) (@lem50507 _5131 _5132 h1)). Qed.
Lemma lem50983 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term4 _5131 _5132) (h2 : term192 _5131 _5132 p P p1 p2) : False.
Proof. exact (or_elim (@lem50494 _5131 _5132 p P p1 p2 h2) (fun h0 : term157 _5131 _5132 p P => @lem50982 _5131 _5132 p P h1 h0) (fun h0 : term122 _5131 _5132 P p1 p2 => @lem50980 _5131 _5132 P p1 p2 h0)). Qed.
Lemma lem50984 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term4 _5131 _5132) (h2 : term192 _5131 _5132 p P p1 p2) : (term192 _5131 _5132 p P p1 p2) = False.
Proof. exact (prop_ext (fun h3 : term192 _5131 _5132 p P p1 p2 => @lem50983 _5131 _5132 p P p1 p2 h1 h2) (fun h3 : False => @lem50494 _5131 _5132 p P p1 p2 h2)). Qed.
Lemma lem50985 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term4 _5131 _5132) (h2 : term192 _5131 _5132 p P p1 p2) : False.
Proof. exact (EQ_MP (@lem50984 _5131 _5132 p P p1 p2 h1 h2) (@lem50494 _5131 _5132 p P p1 p2 h2)). Qed.
Lemma lem50986 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term4 _5131 _5132) (h2 : term192 _5131 _5132 p P p1 p2) : (term4 _5131 _5132) = False.
Proof. exact (prop_ext (fun h3 : term4 _5131 _5132 => @lem50985 _5131 _5132 p P p1 p2 h1 h2) (fun h3 : False => @lem50451 _5131 _5132 h1)). Qed.
Lemma lem50987 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (p2 : _5131) (h1 : term4 _5131 _5132) (h2 : term192 _5131 _5132 p P p1 p2) : False.
Proof. exact (EQ_MP (@lem50986 _5131 _5132 p P p1 p2 h1 h2) (@lem50451 _5131 _5132 h1)). Qed.
Lemma lem50988 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (p1 : _5132) (h1 : term4 _5131 _5132) (h2 : term195 _5131 _5132 p P p1) : False.
Proof. exact (ex_elim (@lem50433 _5131 _5132 p P p1 h2) (fun p2 : _5131 => fun h0 : term194 _5131 _5132 p P p1 p2 => @lem50987 _5131 _5132 p P p1 p2 h1 h0)). Qed.
Lemma lem50989 {_5131 _5132 : Type'} (p : prod _5132 _5131) (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term197 _5131 _5132 p P) : False.
Proof. exact (ex_elim (@lem50432 _5131 _5132 p P h2) (fun p1 : _5132 => fun h0 : term196 _5131 _5132 p P p1 => @lem50988 _5131 _5132 p P p1 h1 h0)). Qed.
Lemma lem50990 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) (h1 : term4 _5131 _5132) (h2 : term199 _5131 _5132 P) : False.
Proof. exact (ex_elim (@lem50431 _5131 _5132 P h2) (fun p : prod _5132 _5131 => fun h0 : term198 _5131 _5132 P p => @lem50989 _5131 _5132 p P h1 h0)). Qed.
Lemma lem50991 {_5131 _5132 : Type'} (h1 : term4 _5131 _5132) (h2 : term3 _5131 _5132) : False.
Proof. exact (ex_elim (@lem50417 _5131 _5132 h2) (fun P : type1223 _5131 _5132 => fun h0 : term200 _5131 _5132 P => @lem50990 _5131 _5132 P h1 h0)). Qed.
Lemma lem50992 {_5131 _5132 : Type'} (h1 : term4 _5131 _5132) (h2 : term3 _5131 _5132) : (term4 _5131 _5132) = False.
Proof. exact (prop_ext (fun h3 : term4 _5131 _5132 => @lem50991 _5131 _5132 h1 h2) (fun h3 : False => @lem50430 _5131 _5132 h1)). Qed.
Lemma lem50993 {_5131 _5132 : Type'} (h1 : term4 _5131 _5132) (h2 : term3 _5131 _5132) : False.
Proof. exact (EQ_MP (@lem50992 _5131 _5132 h1 h2) (@lem50430 _5131 _5132 h1)). Qed.
Lemma lem50994 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : term9 _5131 _5132.
Proof. exact (fun h0 : term4 _5131 _5132 => @lem50993 _5131 _5132 h0 h1). Qed.
Lemma lem50995 {_5131 _5132 : Type'} : (term9 _5131 _5132) = (term10 _5131 _5132).
Proof. exact (@lem69 (term4 _5131 _5132)). Qed.
Lemma lem50996 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : term10 _5131 _5132.
Proof. exact (EQ_MP (@lem50995 _5131 _5132) (@lem50994 _5131 _5132 h1)). Qed.
Lemma lem50997 {_5131 _5132 : Type'} : term12 _5131 _5132.
Proof. exact (fun h0 : term3 _5131 _5132 => @lem50996 _5131 _5132 h0). Qed.
Lemma lem50998 {_5131 _5132 : Type'} : term5 _5131 _5132.
Proof. exact (EQ_MP (@lem50038 _5131 _5132) (@lem50997 _5131 _5132)). Qed.
Lemma lem51000 {_5131 _5132 : Type'} : term5 _5131 _5132.
Proof. exact (@lem49941 _5131 _5132 (@lem50998 _5131 _5132)). Qed.
Lemma lem51001 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : term9 _5131 _5132.
Proof. exact (@lem51000 _5131 _5132 (@lem49924 _5131 _5132 h1)). Qed.
Lemma lem51002 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : False.
Proof. exact (@lem51001 _5131 _5132 h1 (@lem49925 _5131 _5132)). Qed.
Lemma lem51003 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : (term3 _5131 _5132) = False.
Proof. exact (prop_ext (fun h2 : term3 _5131 _5132 => @lem51002 _5131 _5132 h1) (fun h2 : False => @lem49924 _5131 _5132 h1)). Qed.
Lemma lem51004 {_5131 _5132 : Type'} (h1 : term3 _5131 _5132) : False.
Proof. exact (EQ_MP (@lem51003 _5131 _5132 h1) (@lem49924 _5131 _5132 h1)). Qed.
Lemma lem51005 {_5131 _5132 : Type'} : term2 _5131 _5132.
Proof. exact (fun h0 : term3 _5131 _5132 => @lem51004 _5131 _5132 h0). Qed.
Lemma lem51006 {_5131 _5132 : Type'} : term1 _5131 _5132.
Proof. exact (EQ_MP (@lem49923 _5131 _5132) (@lem51005 _5131 _5132)). Qed.
