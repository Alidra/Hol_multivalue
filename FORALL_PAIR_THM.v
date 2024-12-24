Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_PAIR_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import PAIR_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem48933 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem48934 {_5106 _5107 : Type'} : (term1 _5106 _5107) = (term2 _5106 _5107).
Proof. exact (@lem48933 (term1 _5106 _5107)). Qed.
Lemma lem48935 {_5106 _5107 : Type'} : (term2 _5106 _5107) = (term1 _5106 _5107).
Proof. exact (SYM (@lem48934 _5106 _5107)). Qed.
Lemma lem48936 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : term3 _5106 _5107.
Proof. exact (h1). Qed.
Lemma lem48937 {_5106 _5107 : Type'} : term4 _5106 _5107.
Proof. exact (@lem48081 _5107 _5106). Qed.
Lemma lem48940 {_5106 _5107 : Type'} (h1 : term5 _5106 _5107) : term5 _5106 _5107.
Proof. exact (h1). Qed.
Lemma lem48941 {_5106 _5107 : Type'} : term6 _5106 _5107.
Proof. exact (fun h0 : term5 _5106 _5107 => @lem48940 _5106 _5107 h0). Qed.
Lemma lem48942 {_5106 _5107 : Type'} (h1 : term6 _5106 _5107) : term6 _5106 _5107.
Proof. exact (h1). Qed.
Lemma lem48943 {_5106 _5107 : Type'} (h1 : term5 _5106 _5107) : term5 _5106 _5107.
Proof. exact (h1). Qed.
Lemma lem48944 {_5106 _5107 : Type'} (h1 : term5 _5106 _5107) (h2 : term6 _5106 _5107) : term5 _5106 _5107.
Proof. exact (@lem48942 _5106 _5107 h2 (@lem48943 _5106 _5107 h1)). Qed.
Lemma lem48945 {_5106 _5107 : Type'} (h1 : term5 _5106 _5107) : term7 _5106 _5107.
Proof. exact (fun h0 : term6 _5106 _5107 => @lem48944 _5106 _5107 h1 h0). Qed.
Lemma lem48946 {_5106 _5107 : Type'} (h1 : term6 _5106 _5107) : term6 _5106 _5107.
Proof. exact (h1). Qed.
Lemma lem48947 {_5106 _5107 : Type'} (h1 : term5 _5106 _5107) (h2 : term6 _5106 _5107) : term5 _5106 _5107.
Proof. exact (@lem48945 _5106 _5107 h1 (@lem48946 _5106 _5107 h2)). Qed.
Lemma lem48948 {_5106 _5107 : Type'} (h1 : term6 _5106 _5107) : term6 _5106 _5107.
Proof. exact (fun h0 : term5 _5106 _5107 => @lem48947 _5106 _5107 h0 h1). Qed.
Lemma lem48949 {_5106 _5107 : Type'} : term8 _5106 _5107.
Proof. exact (fun h0 : term6 _5106 _5107 => @lem48948 _5106 _5107 h0). Qed.
Lemma lem48952 {_5106 _5107 : Type'} : term6 _5106 _5107.
Proof. exact (@lem48949 _5106 _5107 (@lem48941 _5106 _5107)). Qed.
Lemma lem48953 {_5106 _5107 : Type'} : term6 _5106 _5107.
Proof. exact (@lem48952 _5106 _5107). Qed.
Lemma lem48973 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem48974 {_5106 _5107 : Type'} : (term9 _5106 _5107) = (term10 _5106 _5107).
Proof. exact (@lem48973 (term4 _5106 _5107)). Qed.
Lemma lem48979 {_5106 _5107 : Type'} : (term11 _5106 _5107) = (term11 _5106 _5107).
Proof. exact (eq_refl (term11 _5106 _5107)). Qed.
Lemma lem48986 {_5106 _5107 : Type'} : (term5 _5106 _5107) = (term12 _5106 _5107).
Proof. exact (MK_COMB (@lem48979 _5106 _5107) (@lem48974 _5106 _5107)). Qed.
Lemma lem48987 {_5106 _5107 : Type'} (x : prod _5107 _5106) : ((term13 _5106 _5107 x) = x) = ((term13 _5106 _5107 x) = x).
Proof. exact (eq_refl ((term13 _5106 _5107 x) = x)). Qed.
Lemma lem48988 {_5106 _5107 : Type'} : (term14 _5106 _5107) = (term14 _5106 _5107).
Proof. exact (fun_ext (fun x : prod _5107 _5106 => @lem48987 _5106 _5107 x)). Qed.
Lemma lem48989 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem48990 {_5106 _5107 : Type'} : (term4 _5106 _5107) = (term4 _5106 _5107).
Proof. exact (MK_COMB (@lem48989 _5106 _5107) (@lem48988 _5106 _5107)). Qed.
Lemma lem48991 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem48992 {_5106 _5107 : Type'} : (term10 _5106 _5107) = (term10 _5106 _5107).
Proof. exact (MK_COMB (@lem48991) (@lem48990 _5106 _5107)). Qed.
Lemma lem48993 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term15 _5106 _5107 P p1 p2) = (term15 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term15 _5106 _5107 P p1 p2)). Qed.
Lemma lem48994 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term16 _5106 _5107 P p1) = (term16 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem48993 _5106 _5107 P p1 p2)). Qed.
Lemma lem48995 {_5106 : Type'} : (@all _5106) = (@all _5106).
Proof. exact (eq_refl (@all _5106)). Qed.
Lemma lem48996 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term17 _5106 _5107 P p1) = (term17 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem48995 _5106) (@lem48994 _5106 _5107 P p1)). Qed.
Lemma lem48997 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term18 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem48996 _5106 _5107 P p1)). Qed.
Lemma lem48998 {_5107 : Type'} : (@all _5107) = (@all _5107).
Proof. exact (eq_refl (@all _5107)). Qed.
Lemma lem48999 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term19 _5106 _5107 P).
Proof. exact (MK_COMB (@lem48998 _5107) (@lem48997 _5106 _5107 P)). Qed.
Lemma lem49000 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem49001 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term20 _5106 _5107 P) = (term20 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49000 _5106 _5107 P p)). Qed.
Lemma lem49002 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem49003 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term21 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49002 _5106 _5107) (@lem49001 _5106 _5107 P)). Qed.
Lemma lem49004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49005 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term22 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49004) (@lem49003 _5106 _5107 P)). Qed.
Lemma lem49006 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : ((term21 _5106 _5107 P) = (term19 _5106 _5107 P)) = ((term21 _5106 _5107 P) = (term19 _5106 _5107 P)).
Proof. exact (MK_COMB (@lem49005 _5106 _5107 P) (@lem48999 _5106 _5107 P)). Qed.
Lemma lem49007 {_5106 _5107 : Type'} : (term23 _5106 _5107) = (term23 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49006 _5106 _5107 P)). Qed.
Lemma lem49008 {_5106 _5107 : Type'} : (@all ((prod _5107 _5106) -> Prop)) = (@all ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@all ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49009 {_5106 _5107 : Type'} : (term1 _5106 _5107) = (term1 _5106 _5107).
Proof. exact (MK_COMB (@lem49008 _5106 _5107) (@lem49007 _5106 _5107)). Qed.
Lemma lem49010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem49011 {_5106 _5107 : Type'} : (term3 _5106 _5107) = (term3 _5106 _5107).
Proof. exact (MK_COMB (@lem49010) (@lem49009 _5106 _5107)). Qed.
Lemma lem49012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem49013 {_5106 _5107 : Type'} : (term11 _5106 _5107) = (term11 _5106 _5107).
Proof. exact (MK_COMB (@lem49012) (@lem49011 _5106 _5107)). Qed.
Lemma lem49014 {_5106 _5107 : Type'} : (term12 _5106 _5107) = (term12 _5106 _5107).
Proof. exact (MK_COMB (@lem49013 _5106 _5107) (@lem48992 _5106 _5107)). Qed.
Lemma lem49049 {_5106 _5107 : Type'} : (term5 _5106 _5107) = (term12 _5106 _5107).
Proof. exact (TRANS (@lem48986 _5106 _5107) (@lem49014 _5106 _5107)). Qed.
Lemma lem49050 {_5106 _5107 : Type'} : (term12 _5106 _5107) = (term5 _5106 _5107).
Proof. exact (SYM (@lem49049 _5106 _5107)). Qed.
Lemma lem49051 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : term3 _5106 _5107.
Proof. exact (h1). Qed.
Lemma lem49052 {_5106 _5107 : Type'} (h1 : term4 _5106 _5107) : term4 _5106 _5107.
Proof. exact (h1). Qed.
Lemma lem49054 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem49055 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term24 _5106 _5107 P) = (term25 _5106 _5107 P).
Proof. exact (@lem18392 (prod _5107 _5106) P). Qed.
Lemma lem49056 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term26 _5106 _5107 P) = (term27 _5106 _5107 P).
Proof. exact (@lem49055 _5106 _5107 (term20 _5106 _5107 P)). Qed.
Lemma lem49057 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term28 _5106 _5107 P p) = (P p).
Proof. exact (eq_refl (term28 _5106 _5107 P p)). Qed.
Lemma lem49058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem49060 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term29 _5106 _5107 P p) = (term30 _5106 _5107 P p).
Proof. exact (MK_COMB (@lem49058) (@lem49057 _5106 _5107 P p)). Qed.
Lemma lem49061 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term31 _5106 _5107 P) = (term32 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49060 _5106 _5107 P p)). Qed.
Lemma lem49062 {_5106 _5107 : Type'} : (@ex (prod _5107 _5106)) = (@ex (prod _5107 _5106)).
Proof. exact (eq_refl (@ex (prod _5107 _5106))). Qed.
Lemma lem49063 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term27 _5106 _5107 P) = (term25 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49062 _5106 _5107) (@lem49061 _5106 _5107 P)). Qed.
Lemma lem49064 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term26 _5106 _5107 P) = (term25 _5106 _5107 P).
Proof. exact (TRANS (@lem49056 _5106 _5107 P) (@lem49063 _5106 _5107 P)). Qed.
Lemma lem49065 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term20 _5106 _5107 P) = (term20 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49054 _5106 _5107 P p)). Qed.
Lemma lem49066 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem49067 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term21 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49066 _5106 _5107) (@lem49065 _5106 _5107 P)). Qed.
Lemma lem49069 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term15 _5106 _5107 P p1 p2) = (term15 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term15 _5106 _5107 P p1 p2)). Qed.
Lemma lem49070 {_5106 : Type'} (P : _5106 -> Prop) : (term33 _5106 P) = (term34 _5106 P).
Proof. exact (@lem18392 _5106 P). Qed.
Lemma lem49071 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term35 _5106 _5107 P p1) = (term36 _5106 _5107 P p1).
Proof. exact (@lem49070 _5106 (term16 _5106 _5107 P p1)). Qed.
Lemma lem49072 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term37 _5106 _5107 P p1 p2) = (term15 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term37 _5106 _5107 P p1 p2)). Qed.
Lemma lem49073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem49075 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term38 _5106 _5107 P p1 p2) = (term39 _5106 _5107 P p1 p2).
Proof. exact (MK_COMB (@lem49073) (@lem49072 _5106 _5107 P p1 p2)). Qed.
Lemma lem49076 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term40 _5106 _5107 P p1) = (term41 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49075 _5106 _5107 P p1 p2)). Qed.
Lemma lem49077 {_5106 : Type'} : (@ex _5106) = (@ex _5106).
Proof. exact (eq_refl (@ex _5106)). Qed.
Lemma lem49078 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term36 _5106 _5107 P p1) = (term42 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49077 _5106) (@lem49076 _5106 _5107 P p1)). Qed.
Lemma lem49079 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term35 _5106 _5107 P p1) = (term42 _5106 _5107 P p1).
Proof. exact (TRANS (@lem49071 _5106 _5107 P p1) (@lem49078 _5106 _5107 P p1)). Qed.
Lemma lem49080 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term16 _5106 _5107 P p1) = (term16 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49069 _5106 _5107 P p1 p2)). Qed.
Lemma lem49081 {_5106 : Type'} : (@all _5106) = (@all _5106).
Proof. exact (eq_refl (@all _5106)). Qed.
Lemma lem49082 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term17 _5106 _5107 P p1) = (term17 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49081 _5106) (@lem49080 _5106 _5107 P p1)). Qed.
Lemma lem49083 {_5107 : Type'} (P : _5107 -> Prop) : (term33 _5107 P) = (term34 _5107 P).
Proof. exact (@lem18392 _5107 P). Qed.
Lemma lem49084 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term43 _5106 _5107 P) = (term44 _5106 _5107 P).
Proof. exact (@lem49083 _5107 (term18 _5106 _5107 P)). Qed.
Lemma lem49085 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term45 _5106 _5107 P p1) = (term17 _5106 _5107 P p1).
Proof. exact (eq_refl (term45 _5106 _5107 P p1)). Qed.
Lemma lem49086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem49087 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term46 _5106 _5107 P p1) = (term35 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49086) (@lem49085 _5106 _5107 P p1)). Qed.
Lemma lem49088 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term46 _5106 _5107 P p1) = (term42 _5106 _5107 P p1).
Proof. exact (TRANS (@lem49087 _5106 _5107 P p1) (@lem49079 _5106 _5107 P p1)). Qed.
Lemma lem49089 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term47 _5106 _5107 P) = (term48 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49088 _5106 _5107 P p1)). Qed.
Lemma lem49090 {_5107 : Type'} : (@ex _5107) = (@ex _5107).
Proof. exact (eq_refl (@ex _5107)). Qed.
Lemma lem49091 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term44 _5106 _5107 P) = (term49 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49090 _5107) (@lem49089 _5106 _5107 P)). Qed.
Lemma lem49092 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term43 _5106 _5107 P) = (term49 _5106 _5107 P).
Proof. exact (TRANS (@lem49084 _5106 _5107 P) (@lem49091 _5106 _5107 P)). Qed.
Lemma lem49093 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term18 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49082 _5106 _5107 P p1)). Qed.
Lemma lem49094 {_5107 : Type'} : (@all _5107) = (@all _5107).
Proof. exact (eq_refl (@all _5107)). Qed.
Lemma lem49095 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term19 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49094 _5107) (@lem49093 _5106 _5107 P)). Qed.
Lemma lem49096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem49097 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term50 _5106 _5107 P) = (term51 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49096) (@lem49064 _5106 _5107 P)). Qed.
Lemma lem49098 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term52 _5106 _5107 P) = (term53 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49097 _5106 _5107 P) (@lem49095 _5106 _5107 P)). Qed.
Lemma lem49099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem49100 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term54 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49099) (@lem49067 _5106 _5107 P)). Qed.
Lemma lem49101 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term55 _5106 _5107 P) = (term56 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49100 _5106 _5107 P) (@lem49092 _5106 _5107 P)). Qed.
Lemma lem49102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49103 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term57 _5106 _5107 P) = (term58 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49102) (@lem49101 _5106 _5107 P)). Qed.
Lemma lem49104 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term59 _5106 _5107 P) = (term60 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49103 _5106 _5107 P) (@lem49098 _5106 _5107 P)). Qed.
Lemma lem49105 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term61 _5106 _5107 P) = (term59 _5106 _5107 P).
Proof. exact (@lem17646 (term21 _5106 _5107 P) (term19 _5106 _5107 P)). Qed.
Lemma lem49106 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term61 _5106 _5107 P) = (term60 _5106 _5107 P).
Proof. exact (TRANS (@lem49105 _5106 _5107 P) (@lem49104 _5106 _5107 P)). Qed.
Lemma lem49107 {_5106 _5107 : Type'} (P : type330 _5106 _5107) : (term62 _5106 _5107 P) = (term63 _5106 _5107 P).
Proof. exact (@lem18392 (type1223 _5106 _5107) P). Qed.
Lemma lem49108 {_5106 _5107 : Type'} : (term3 _5106 _5107) = (term64 _5106 _5107).
Proof. exact (@lem49107 _5106 _5107 (term23 _5106 _5107)). Qed.
Lemma lem49109 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term65 _5106 _5107 P) = ((term21 _5106 _5107 P) = (term19 _5106 _5107 P)).
Proof. exact (eq_refl (term65 _5106 _5107 P)). Qed.
Lemma lem49110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem49111 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term66 _5106 _5107 P) = (term61 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49110) (@lem49109 _5106 _5107 P)). Qed.
Lemma lem49112 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term66 _5106 _5107 P) = (term60 _5106 _5107 P).
Proof. exact (TRANS (@lem49111 _5106 _5107 P) (@lem49106 _5106 _5107 P)). Qed.
Lemma lem49113 {_5106 _5107 : Type'} : (term67 _5106 _5107) = (term68 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49112 _5106 _5107 P)). Qed.
Lemma lem49114 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49115 {_5106 _5107 : Type'} : (term64 _5106 _5107) = (term69 _5106 _5107).
Proof. exact (MK_COMB (@lem49114 _5106 _5107) (@lem49113 _5106 _5107)). Qed.
Lemma lem49116 {_5106 _5107 : Type'} : (term3 _5106 _5107) = (term69 _5106 _5107).
Proof. exact (TRANS (@lem49108 _5106 _5107) (@lem49115 _5106 _5107)). Qed.
Lemma lem49118 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem49119 {_5106 _5107 : Type'} (P : type330 _5106 _5107) (Q : type330 _5106 _5107) : (term72 _5106 _5107 P Q) = (term73 _5106 _5107 P Q).
Proof. exact (@lem49118 (type1223 _5106 _5107) P Q). Qed.
Lemma lem49120 {_5106 _5107 : Type'} : (term74 _5106 _5107) = (term75 _5106 _5107).
Proof. exact (@lem49119 _5106 _5107 (term76 _5106 _5107) (term77 _5106 _5107)). Qed.
Lemma lem49121 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term78 _5106 _5107 P) = (term56 _5106 _5107 P).
Proof. exact (eq_refl (term78 _5106 _5107 P)). Qed.
Lemma lem49122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49123 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term79 _5106 _5107 P) = (term58 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49122) (@lem49121 _5106 _5107 P)). Qed.
Lemma lem49124 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term80 _5106 _5107 P) = (term53 _5106 _5107 P).
Proof. exact (eq_refl (term80 _5106 _5107 P)). Qed.
Lemma lem49125 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term81 _5106 _5107 P) = (term60 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49123 _5106 _5107 P) (@lem49124 _5106 _5107 P)). Qed.
Lemma lem49126 {_5106 _5107 : Type'} : (term82 _5106 _5107) = (term68 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49125 _5106 _5107 P)). Qed.
Lemma lem49127 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49128 {_5106 _5107 : Type'} : (term74 _5106 _5107) = (term69 _5106 _5107).
Proof. exact (MK_COMB (@lem49127 _5106 _5107) (@lem49126 _5106 _5107)). Qed.
Lemma lem49129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49130 {_5106 _5107 : Type'} : (term83 _5106 _5107) = (term84 _5106 _5107).
Proof. exact (MK_COMB (@lem49129) (@lem49128 _5106 _5107)). Qed.
Lemma lem49131 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term78 _5106 _5107 P) = (term56 _5106 _5107 P).
Proof. exact (eq_refl (term78 _5106 _5107 P)). Qed.
Lemma lem49132 {_5106 _5107 : Type'} : (term85 _5106 _5107) = (term76 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49131 _5106 _5107 P)). Qed.
Lemma lem49133 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49134 {_5106 _5107 : Type'} : (term86 _5106 _5107) = (term87 _5106 _5107).
Proof. exact (MK_COMB (@lem49133 _5106 _5107) (@lem49132 _5106 _5107)). Qed.
Lemma lem49135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49136 {_5106 _5107 : Type'} : (term88 _5106 _5107) = (term89 _5106 _5107).
Proof. exact (MK_COMB (@lem49135) (@lem49134 _5106 _5107)). Qed.
Lemma lem49137 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term80 _5106 _5107 P) = (term53 _5106 _5107 P).
Proof. exact (eq_refl (term80 _5106 _5107 P)). Qed.
Lemma lem49138 {_5106 _5107 : Type'} : (term90 _5106 _5107) = (term77 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49137 _5106 _5107 P)). Qed.
Lemma lem49139 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49140 {_5106 _5107 : Type'} : (term91 _5106 _5107) = (term92 _5106 _5107).
Proof. exact (MK_COMB (@lem49139 _5106 _5107) (@lem49138 _5106 _5107)). Qed.
Lemma lem49141 {_5106 _5107 : Type'} : (term75 _5106 _5107) = (term93 _5106 _5107).
Proof. exact (MK_COMB (@lem49136 _5106 _5107) (@lem49140 _5106 _5107)). Qed.
Lemma lem49142 {_5106 _5107 : Type'} : ((term74 _5106 _5107) = (term75 _5106 _5107)) = ((term69 _5106 _5107) = (term93 _5106 _5107)).
Proof. exact (MK_COMB (@lem49130 _5106 _5107) (@lem49141 _5106 _5107)). Qed.
Lemma lem49143 {_5106 _5107 : Type'} : (term69 _5106 _5107) = (term93 _5106 _5107).
Proof. exact (EQ_MP (@lem49142 _5106 _5107) (@lem49120 _5106 _5107)). Qed.
Lemma lem49265 {A : Type'} (P : Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem49266 {_5107 : Type'} (P : Prop) (Q : _5107 -> Prop) : (term94 _5107 P Q) = (term95 _5107 P Q).
Proof. exact (@lem49265 _5107 P Q). Qed.
Lemma lem49267 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term96 _5106 _5107 P) = (term97 _5106 _5107 P).
Proof. exact (@lem49266 _5107 (term21 _5106 _5107 P) (term48 _5106 _5107 P)). Qed.
Lemma lem49268 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term98 _5106 _5107 P p1) = (term42 _5106 _5107 P p1).
Proof. exact (eq_refl (term98 _5106 _5107 P p1)). Qed.
Lemma lem49269 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term99 _5106 _5107 P) = (term48 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49268 _5106 _5107 P p1)). Qed.
Lemma lem49270 {_5107 : Type'} : (@ex _5107) = (@ex _5107).
Proof. exact (eq_refl (@ex _5107)). Qed.
Lemma lem49271 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term100 _5106 _5107 P) = (term49 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49270 _5107) (@lem49269 _5106 _5107 P)). Qed.
Lemma lem49272 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term54 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (eq_refl (term54 _5106 _5107 P)). Qed.
Lemma lem49273 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term96 _5106 _5107 P) = (term56 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49272 _5106 _5107 P) (@lem49271 _5106 _5107 P)). Qed.
Lemma lem49274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49275 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term101 _5106 _5107 P) = (term102 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49274) (@lem49273 _5106 _5107 P)). Qed.
Lemma lem49276 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term98 _5106 _5107 P p1) = (term42 _5106 _5107 P p1).
Proof. exact (eq_refl (term98 _5106 _5107 P p1)). Qed.
Lemma lem49277 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term54 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (eq_refl (term54 _5106 _5107 P)). Qed.
Lemma lem49278 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term103 _5106 _5107 P p1) = (term104 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49277 _5106 _5107 P) (@lem49276 _5106 _5107 P p1)). Qed.
Lemma lem49279 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term105 _5106 _5107 P) = (term106 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49278 _5106 _5107 P p1)). Qed.
Lemma lem49280 {_5107 : Type'} : (@ex _5107) = (@ex _5107).
Proof. exact (eq_refl (@ex _5107)). Qed.
Lemma lem49281 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term97 _5106 _5107 P) = (term107 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49280 _5107) (@lem49279 _5106 _5107 P)). Qed.
Lemma lem49282 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : ((term96 _5106 _5107 P) = (term97 _5106 _5107 P)) = ((term56 _5106 _5107 P) = (term107 _5106 _5107 P)).
Proof. exact (MK_COMB (@lem49275 _5106 _5107 P) (@lem49281 _5106 _5107 P)). Qed.
Lemma lem49283 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term56 _5106 _5107 P) = (term107 _5106 _5107 P).
Proof. exact (EQ_MP (@lem49282 _5106 _5107 P) (@lem49267 _5106 _5107 P)). Qed.
Lemma lem49285 {A : Type'} (P : Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem49286 {_5106 : Type'} (P : Prop) (Q : _5106 -> Prop) : (term94 _5106 P Q) = (term95 _5106 P Q).
Proof. exact (@lem49285 _5106 P Q). Qed.
Lemma lem49287 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term108 _5106 _5107 P p1) = (term109 _5106 _5107 P p1).
Proof. exact (@lem49286 _5106 (term21 _5106 _5107 P) (term41 _5106 _5107 P p1)). Qed.
Lemma lem49288 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term110 _5106 _5107 P p1 p2) = (term39 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term110 _5106 _5107 P p1 p2)). Qed.
Lemma lem49289 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term111 _5106 _5107 P p1) = (term41 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49288 _5106 _5107 P p1 p2)). Qed.
Lemma lem49290 {_5106 : Type'} : (@ex _5106) = (@ex _5106).
Proof. exact (eq_refl (@ex _5106)). Qed.
Lemma lem49291 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term112 _5106 _5107 P p1) = (term42 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49290 _5106) (@lem49289 _5106 _5107 P p1)). Qed.
Lemma lem49292 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term54 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (eq_refl (term54 _5106 _5107 P)). Qed.
Lemma lem49293 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term108 _5106 _5107 P p1) = (term104 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49292 _5106 _5107 P) (@lem49291 _5106 _5107 P p1)). Qed.
Lemma lem49294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49295 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term113 _5106 _5107 P p1) = (term114 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49294) (@lem49293 _5106 _5107 P p1)). Qed.
Lemma lem49296 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term110 _5106 _5107 P p1 p2) = (term39 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term110 _5106 _5107 P p1 p2)). Qed.
Lemma lem49297 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term54 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (eq_refl (term54 _5106 _5107 P)). Qed.
Lemma lem49298 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term115 _5106 _5107 P p1 p2) = (term116 _5106 _5107 P p1 p2).
Proof. exact (MK_COMB (@lem49297 _5106 _5107 P) (@lem49296 _5106 _5107 P p1 p2)). Qed.
Lemma lem49299 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term117 _5106 _5107 P p1) = (term118 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49298 _5106 _5107 P p1 p2)). Qed.
Lemma lem49300 {_5106 : Type'} : (@ex _5106) = (@ex _5106).
Proof. exact (eq_refl (@ex _5106)). Qed.
Lemma lem49301 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term109 _5106 _5107 P p1) = (term119 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49300 _5106) (@lem49299 _5106 _5107 P p1)). Qed.
Lemma lem49302 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : ((term108 _5106 _5107 P p1) = (term109 _5106 _5107 P p1)) = ((term104 _5106 _5107 P p1) = (term119 _5106 _5107 P p1)).
Proof. exact (MK_COMB (@lem49295 _5106 _5107 P p1) (@lem49301 _5106 _5107 P p1)). Qed.
Lemma lem49303 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term104 _5106 _5107 P p1) = (term119 _5106 _5107 P p1).
Proof. exact (EQ_MP (@lem49302 _5106 _5107 P p1) (@lem49287 _5106 _5107 P p1)). Qed.
Lemma lem49304 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term106 _5106 _5107 P) = (term120 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49303 _5106 _5107 P p1)). Qed.
Lemma lem49305 {_5107 : Type'} : (@ex _5107) = (@ex _5107).
Proof. exact (eq_refl (@ex _5107)). Qed.
Lemma lem49306 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term107 _5106 _5107 P) = (term121 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49305 _5107) (@lem49304 _5106 _5107 P)). Qed.
Lemma lem49307 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term56 _5106 _5107 P) = (term121 _5106 _5107 P).
Proof. exact (TRANS (@lem49283 _5106 _5107 P) (@lem49306 _5106 _5107 P)). Qed.
Lemma lem49308 {_5106 _5107 : Type'} : (term76 _5106 _5107) = (term122 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49307 _5106 _5107 P)). Qed.
Lemma lem49309 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49310 {_5106 _5107 : Type'} : (term87 _5106 _5107) = (term123 _5106 _5107).
Proof. exact (MK_COMB (@lem49309 _5106 _5107) (@lem49308 _5106 _5107)). Qed.
Lemma lem49311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49312 {_5106 _5107 : Type'} : (term89 _5106 _5107) = (term124 _5106 _5107).
Proof. exact (MK_COMB (@lem49311) (@lem49310 _5106 _5107)). Qed.
Lemma lem49314 {A : Type'} (P : A -> Prop) (Q : Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem49315 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (Q : Prop) : (term127 _5106 _5107 P Q) = (term128 _5106 _5107 P Q).
Proof. exact (@lem49314 (prod _5107 _5106) P Q). Qed.
Lemma lem49316 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term129 _5106 _5107 P) = (term130 _5106 _5107 P).
Proof. exact (@lem49315 _5106 _5107 (term32 _5106 _5107 P) (term19 _5106 _5107 P)). Qed.
Lemma lem49317 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term131 _5106 _5107 P p) = (term30 _5106 _5107 P p).
Proof. exact (eq_refl (term131 _5106 _5107 P p)). Qed.
Lemma lem49318 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term132 _5106 _5107 P) = (term32 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49317 _5106 _5107 P p)). Qed.
Lemma lem49319 {_5106 _5107 : Type'} : (@ex (prod _5107 _5106)) = (@ex (prod _5107 _5106)).
Proof. exact (eq_refl (@ex (prod _5107 _5106))). Qed.
Lemma lem49320 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term133 _5106 _5107 P) = (term25 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49319 _5106 _5107) (@lem49318 _5106 _5107 P)). Qed.
Lemma lem49321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem49322 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term134 _5106 _5107 P) = (term51 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49321) (@lem49320 _5106 _5107 P)). Qed.
Lemma lem49323 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term19 _5106 _5107 P).
Proof. exact (eq_refl (term19 _5106 _5107 P)). Qed.
Lemma lem49324 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term129 _5106 _5107 P) = (term53 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49322 _5106 _5107 P) (@lem49323 _5106 _5107 P)). Qed.
Lemma lem49325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49326 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term135 _5106 _5107 P) = (term136 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49325) (@lem49324 _5106 _5107 P)). Qed.
Lemma lem49327 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term131 _5106 _5107 P p) = (term30 _5106 _5107 P p).
Proof. exact (eq_refl (term131 _5106 _5107 P p)). Qed.
Lemma lem49328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem49329 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term137 _5106 _5107 P p) = (term138 _5106 _5107 P p).
Proof. exact (MK_COMB (@lem49328) (@lem49327 _5106 _5107 P p)). Qed.
Lemma lem49330 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term19 _5106 _5107 P).
Proof. exact (eq_refl (term19 _5106 _5107 P)). Qed.
Lemma lem49331 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) : (term139 _5106 _5107 p P) = (term140 _5106 _5107 p P).
Proof. exact (MK_COMB (@lem49329 _5106 _5107 P p) (@lem49330 _5106 _5107 P)). Qed.
Lemma lem49332 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term141 _5106 _5107 P) = (term142 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49331 _5106 _5107 p P)). Qed.
Lemma lem49333 {_5106 _5107 : Type'} : (@ex (prod _5107 _5106)) = (@ex (prod _5107 _5106)).
Proof. exact (eq_refl (@ex (prod _5107 _5106))). Qed.
Lemma lem49334 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term130 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49333 _5106 _5107) (@lem49332 _5106 _5107 P)). Qed.
Lemma lem49335 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : ((term129 _5106 _5107 P) = (term130 _5106 _5107 P)) = ((term53 _5106 _5107 P) = (term143 _5106 _5107 P)).
Proof. exact (MK_COMB (@lem49326 _5106 _5107 P) (@lem49334 _5106 _5107 P)). Qed.
Lemma lem49336 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term53 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (EQ_MP (@lem49335 _5106 _5107 P) (@lem49316 _5106 _5107 P)). Qed.
Lemma lem49337 {_5106 _5107 : Type'} : (term77 _5106 _5107) = (term144 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49336 _5106 _5107 P)). Qed.
Lemma lem49338 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49339 {_5106 _5107 : Type'} : (term92 _5106 _5107) = (term145 _5106 _5107).
Proof. exact (MK_COMB (@lem49338 _5106 _5107) (@lem49337 _5106 _5107)). Qed.
Lemma lem49340 {_5106 _5107 : Type'} : (term93 _5106 _5107) = (term146 _5106 _5107).
Proof. exact (MK_COMB (@lem49312 _5106 _5107) (@lem49339 _5106 _5107)). Qed.
Lemma lem49342 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem49343 {_5106 _5107 : Type'} (P : type330 _5106 _5107) (Q : type330 _5106 _5107) : (term73 _5106 _5107 P Q) = (term72 _5106 _5107 P Q).
Proof. exact (@lem49342 (type1223 _5106 _5107) P Q). Qed.
Lemma lem49344 {_5106 _5107 : Type'} : (term147 _5106 _5107) = (term148 _5106 _5107).
Proof. exact (@lem49343 _5106 _5107 (term122 _5106 _5107) (term144 _5106 _5107)). Qed.
Lemma lem49345 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term149 _5106 _5107 P) = (term121 _5106 _5107 P).
Proof. exact (eq_refl (term149 _5106 _5107 P)). Qed.
Lemma lem49346 {_5106 _5107 : Type'} : (term150 _5106 _5107) = (term122 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49345 _5106 _5107 P)). Qed.
Lemma lem49347 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49348 {_5106 _5107 : Type'} : (term151 _5106 _5107) = (term123 _5106 _5107).
Proof. exact (MK_COMB (@lem49347 _5106 _5107) (@lem49346 _5106 _5107)). Qed.
Lemma lem49349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49350 {_5106 _5107 : Type'} : (term152 _5106 _5107) = (term124 _5106 _5107).
Proof. exact (MK_COMB (@lem49349) (@lem49348 _5106 _5107)). Qed.
Lemma lem49351 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term153 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (eq_refl (term153 _5106 _5107 P)). Qed.
Lemma lem49352 {_5106 _5107 : Type'} : (term154 _5106 _5107) = (term144 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49351 _5106 _5107 P)). Qed.
Lemma lem49353 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49354 {_5106 _5107 : Type'} : (term155 _5106 _5107) = (term145 _5106 _5107).
Proof. exact (MK_COMB (@lem49353 _5106 _5107) (@lem49352 _5106 _5107)). Qed.
Lemma lem49355 {_5106 _5107 : Type'} : (term147 _5106 _5107) = (term146 _5106 _5107).
Proof. exact (MK_COMB (@lem49350 _5106 _5107) (@lem49354 _5106 _5107)). Qed.
Lemma lem49356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49357 {_5106 _5107 : Type'} : (term156 _5106 _5107) = (term157 _5106 _5107).
Proof. exact (MK_COMB (@lem49356) (@lem49355 _5106 _5107)). Qed.
Lemma lem49358 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term149 _5106 _5107 P) = (term121 _5106 _5107 P).
Proof. exact (eq_refl (term149 _5106 _5107 P)). Qed.
Lemma lem49359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49360 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term158 _5106 _5107 P) = (term159 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49359) (@lem49358 _5106 _5107 P)). Qed.
Lemma lem49361 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term153 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (eq_refl (term153 _5106 _5107 P)). Qed.
Lemma lem49362 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term160 _5106 _5107 P) = (term161 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49360 _5106 _5107 P) (@lem49361 _5106 _5107 P)). Qed.
Lemma lem49363 {_5106 _5107 : Type'} : (term162 _5106 _5107) = (term163 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49362 _5106 _5107 P)). Qed.
Lemma lem49364 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49365 {_5106 _5107 : Type'} : (term148 _5106 _5107) = (term164 _5106 _5107).
Proof. exact (MK_COMB (@lem49364 _5106 _5107) (@lem49363 _5106 _5107)). Qed.
Lemma lem49366 {_5106 _5107 : Type'} : ((term147 _5106 _5107) = (term148 _5106 _5107)) = ((term146 _5106 _5107) = (term164 _5106 _5107)).
Proof. exact (MK_COMB (@lem49357 _5106 _5107) (@lem49365 _5106 _5107)). Qed.
Lemma lem49367 {_5106 _5107 : Type'} : (term146 _5106 _5107) = (term164 _5106 _5107).
Proof. exact (EQ_MP (@lem49366 _5106 _5107) (@lem49344 _5106 _5107)). Qed.
Lemma lem49371 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem49372 {_5107 : Type'} (P : _5107 -> Prop) (Q : Prop) : (term165 _5107 P Q) = (term166 _5107 P Q).
Proof. exact (@lem49371 _5107 P Q). Qed.
Lemma lem49373 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term167 _5106 _5107 P) = (term168 _5106 _5107 P).
Proof. exact (@lem49372 _5107 (term120 _5106 _5107 P) (term143 _5106 _5107 P)). Qed.
Lemma lem49374 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term169 _5106 _5107 P p1) = (term119 _5106 _5107 P p1).
Proof. exact (eq_refl (term169 _5106 _5107 P p1)). Qed.
Lemma lem49375 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term170 _5106 _5107 P) = (term120 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49374 _5106 _5107 P p1)). Qed.
Lemma lem49376 {_5107 : Type'} : (@ex _5107) = (@ex _5107).
Proof. exact (eq_refl (@ex _5107)). Qed.
Lemma lem49377 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term171 _5106 _5107 P) = (term121 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49376 _5107) (@lem49375 _5106 _5107 P)). Qed.
Lemma lem49378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49379 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term172 _5106 _5107 P) = (term159 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49378) (@lem49377 _5106 _5107 P)). Qed.
Lemma lem49380 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term143 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (eq_refl (term143 _5106 _5107 P)). Qed.
Lemma lem49381 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term167 _5106 _5107 P) = (term161 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49379 _5106 _5107 P) (@lem49380 _5106 _5107 P)). Qed.
Lemma lem49382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49383 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term173 _5106 _5107 P) = (term174 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49382) (@lem49381 _5106 _5107 P)). Qed.
Lemma lem49384 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term169 _5106 _5107 P p1) = (term119 _5106 _5107 P p1).
Proof. exact (eq_refl (term169 _5106 _5107 P p1)). Qed.
Lemma lem49385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49386 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term175 _5106 _5107 P p1) = (term176 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49385) (@lem49384 _5106 _5107 P p1)). Qed.
Lemma lem49387 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term143 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (eq_refl (term143 _5106 _5107 P)). Qed.
Lemma lem49388 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term177 _5106 _5107 p1 P) = (term178 _5106 _5107 p1 P).
Proof. exact (MK_COMB (@lem49386 _5106 _5107 P p1) (@lem49387 _5106 _5107 P)). Qed.
Lemma lem49389 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term179 _5106 _5107 P) = (term180 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49388 _5106 _5107 p1 P)). Qed.
Lemma lem49390 {_5107 : Type'} : (@ex _5107) = (@ex _5107).
Proof. exact (eq_refl (@ex _5107)). Qed.
Lemma lem49391 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term168 _5106 _5107 P) = (term181 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49390 _5107) (@lem49389 _5106 _5107 P)). Qed.
Lemma lem49392 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : ((term167 _5106 _5107 P) = (term168 _5106 _5107 P)) = ((term161 _5106 _5107 P) = (term181 _5106 _5107 P)).
Proof. exact (MK_COMB (@lem49383 _5106 _5107 P) (@lem49391 _5106 _5107 P)). Qed.
Lemma lem49393 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term161 _5106 _5107 P) = (term181 _5106 _5107 P).
Proof. exact (EQ_MP (@lem49392 _5106 _5107 P) (@lem49373 _5106 _5107 P)). Qed.
Lemma lem49397 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem49398 {_5106 : Type'} (P : _5106 -> Prop) (Q : Prop) : (term165 _5106 P Q) = (term166 _5106 P Q).
Proof. exact (@lem49397 _5106 P Q). Qed.
Lemma lem49399 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term182 _5106 _5107 p1 P) = (term183 _5106 _5107 p1 P).
Proof. exact (@lem49398 _5106 (term118 _5106 _5107 P p1) (term143 _5106 _5107 P)). Qed.
Lemma lem49400 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term184 _5106 _5107 P p1 p2) = (term116 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term184 _5106 _5107 P p1 p2)). Qed.
Lemma lem49401 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term185 _5106 _5107 P p1) = (term118 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49400 _5106 _5107 P p1 p2)). Qed.
Lemma lem49402 {_5106 : Type'} : (@ex _5106) = (@ex _5106).
Proof. exact (eq_refl (@ex _5106)). Qed.
Lemma lem49403 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term186 _5106 _5107 P p1) = (term119 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49402 _5106) (@lem49401 _5106 _5107 P p1)). Qed.
Lemma lem49404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49405 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term187 _5106 _5107 P p1) = (term176 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49404) (@lem49403 _5106 _5107 P p1)). Qed.
Lemma lem49406 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term143 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (eq_refl (term143 _5106 _5107 P)). Qed.
Lemma lem49407 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term182 _5106 _5107 p1 P) = (term178 _5106 _5107 p1 P).
Proof. exact (MK_COMB (@lem49405 _5106 _5107 P p1) (@lem49406 _5106 _5107 P)). Qed.
Lemma lem49408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49409 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term188 _5106 _5107 p1 P) = (term189 _5106 _5107 p1 P).
Proof. exact (MK_COMB (@lem49408) (@lem49407 _5106 _5107 p1 P)). Qed.
Lemma lem49410 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term184 _5106 _5107 P p1 p2) = (term116 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term184 _5106 _5107 P p1 p2)). Qed.
Lemma lem49411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49412 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term190 _5106 _5107 P p1 p2) = (term191 _5106 _5107 P p1 p2).
Proof. exact (MK_COMB (@lem49411) (@lem49410 _5106 _5107 P p1 p2)). Qed.
Lemma lem49413 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term143 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (eq_refl (term143 _5106 _5107 P)). Qed.
Lemma lem49414 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : (term192 _5106 _5107 p1 p2 P) = (term193 _5106 _5107 p1 p2 P).
Proof. exact (MK_COMB (@lem49412 _5106 _5107 P p1 p2) (@lem49413 _5106 _5107 P)). Qed.
Lemma lem49415 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term194 _5106 _5107 p1 P) = (term195 _5106 _5107 p1 P).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49414 _5106 _5107 p1 p2 P)). Qed.
Lemma lem49416 {_5106 : Type'} : (@ex _5106) = (@ex _5106).
Proof. exact (eq_refl (@ex _5106)). Qed.
Lemma lem49417 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term183 _5106 _5107 p1 P) = (term196 _5106 _5107 p1 P).
Proof. exact (MK_COMB (@lem49416 _5106) (@lem49415 _5106 _5107 p1 P)). Qed.
Lemma lem49418 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : ((term182 _5106 _5107 p1 P) = (term183 _5106 _5107 p1 P)) = ((term178 _5106 _5107 p1 P) = (term196 _5106 _5107 p1 P)).
Proof. exact (MK_COMB (@lem49409 _5106 _5107 p1 P) (@lem49417 _5106 _5107 p1 P)). Qed.
Lemma lem49419 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term178 _5106 _5107 p1 P) = (term196 _5106 _5107 p1 P).
Proof. exact (EQ_MP (@lem49418 _5106 _5107 p1 P) (@lem49399 _5106 _5107 p1 P)). Qed.
Lemma lem49421 {A : Type'} (P : Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem49422 {_5106 _5107 : Type'} (P : Prop) (Q : type1223 _5106 _5107) : (term199 _5106 _5107 P Q) = (term200 _5106 _5107 P Q).
Proof. exact (@lem49421 (prod _5107 _5106) P Q). Qed.
Lemma lem49423 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : (term201 _5106 _5107 p1 p2 P) = (term202 _5106 _5107 p1 p2 P).
Proof. exact (@lem49422 _5106 _5107 (term116 _5106 _5107 P p1 p2) (term142 _5106 _5107 P)). Qed.
Lemma lem49424 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) : (term203 _5106 _5107 P p) = (term140 _5106 _5107 p P).
Proof. exact (eq_refl (term203 _5106 _5107 P p)). Qed.
Lemma lem49425 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term204 _5106 _5107 P) = (term142 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49424 _5106 _5107 p P)). Qed.
Lemma lem49426 {_5106 _5107 : Type'} : (@ex (prod _5107 _5106)) = (@ex (prod _5107 _5106)).
Proof. exact (eq_refl (@ex (prod _5107 _5106))). Qed.
Lemma lem49427 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term205 _5106 _5107 P) = (term143 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49426 _5106 _5107) (@lem49425 _5106 _5107 P)). Qed.
Lemma lem49428 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term191 _5106 _5107 P p1 p2) = (term191 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term191 _5106 _5107 P p1 p2)). Qed.
Lemma lem49429 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : (term201 _5106 _5107 p1 p2 P) = (term193 _5106 _5107 p1 p2 P).
Proof. exact (MK_COMB (@lem49428 _5106 _5107 P p1 p2) (@lem49427 _5106 _5107 P)). Qed.
Lemma lem49430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49431 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : (term206 _5106 _5107 p1 p2 P) = (term207 _5106 _5107 p1 p2 P).
Proof. exact (MK_COMB (@lem49430) (@lem49429 _5106 _5107 p1 p2 P)). Qed.
Lemma lem49432 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) : (term203 _5106 _5107 P p) = (term140 _5106 _5107 p P).
Proof. exact (eq_refl (term203 _5106 _5107 P p)). Qed.
Lemma lem49433 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term191 _5106 _5107 P p1 p2) = (term191 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term191 _5106 _5107 P p1 p2)). Qed.
Lemma lem49434 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) : (term208 _5106 _5107 p1 p2 P p) = (term209 _5106 _5107 p1 p2 p P).
Proof. exact (MK_COMB (@lem49433 _5106 _5107 P p1 p2) (@lem49432 _5106 _5107 p P)). Qed.
Lemma lem49435 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : (term210 _5106 _5107 p1 p2 P) = (term211 _5106 _5107 p1 p2 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49434 _5106 _5107 p1 p2 p P)). Qed.
Lemma lem49436 {_5106 _5107 : Type'} : (@ex (prod _5107 _5106)) = (@ex (prod _5107 _5106)).
Proof. exact (eq_refl (@ex (prod _5107 _5106))). Qed.
Lemma lem49437 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : (term202 _5106 _5107 p1 p2 P) = (term212 _5106 _5107 p1 p2 P).
Proof. exact (MK_COMB (@lem49436 _5106 _5107) (@lem49435 _5106 _5107 p1 p2 P)). Qed.
Lemma lem49438 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : ((term201 _5106 _5107 p1 p2 P) = (term202 _5106 _5107 p1 p2 P)) = ((term193 _5106 _5107 p1 p2 P) = (term212 _5106 _5107 p1 p2 P)).
Proof. exact (MK_COMB (@lem49431 _5106 _5107 p1 p2 P) (@lem49437 _5106 _5107 p1 p2 P)). Qed.
Lemma lem49439 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) : (term193 _5106 _5107 p1 p2 P) = (term212 _5106 _5107 p1 p2 P).
Proof. exact (EQ_MP (@lem49438 _5106 _5107 p1 p2 P) (@lem49423 _5106 _5107 p1 p2 P)). Qed.
Lemma lem49440 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term195 _5106 _5107 p1 P) = (term213 _5106 _5107 p1 P).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49439 _5106 _5107 p1 p2 P)). Qed.
Lemma lem49441 {_5106 : Type'} : (@ex _5106) = (@ex _5106).
Proof. exact (eq_refl (@ex _5106)). Qed.
Lemma lem49442 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term196 _5106 _5107 p1 P) = (term214 _5106 _5107 p1 P).
Proof. exact (MK_COMB (@lem49441 _5106) (@lem49440 _5106 _5107 p1 P)). Qed.
Lemma lem49443 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) : (term178 _5106 _5107 p1 P) = (term214 _5106 _5107 p1 P).
Proof. exact (TRANS (@lem49419 _5106 _5107 p1 P) (@lem49442 _5106 _5107 p1 P)). Qed.
Lemma lem49444 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term180 _5106 _5107 P) = (term215 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49443 _5106 _5107 p1 P)). Qed.
Lemma lem49445 {_5107 : Type'} : (@ex _5107) = (@ex _5107).
Proof. exact (eq_refl (@ex _5107)). Qed.
Lemma lem49446 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term181 _5106 _5107 P) = (term216 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49445 _5107) (@lem49444 _5106 _5107 P)). Qed.
Lemma lem49447 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term161 _5106 _5107 P) = (term216 _5106 _5107 P).
Proof. exact (TRANS (@lem49393 _5106 _5107 P) (@lem49446 _5106 _5107 P)). Qed.
Lemma lem49448 {_5106 _5107 : Type'} : (term163 _5106 _5107) = (term217 _5106 _5107).
Proof. exact (fun_ext (fun P : type1223 _5106 _5107 => @lem49447 _5106 _5107 P)). Qed.
Lemma lem49449 {_5106 _5107 : Type'} : (@ex ((prod _5107 _5106) -> Prop)) = (@ex ((prod _5107 _5106) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5107 _5106) -> Prop))). Qed.
Lemma lem49450 {_5106 _5107 : Type'} : (term164 _5106 _5107) = (term218 _5106 _5107).
Proof. exact (MK_COMB (@lem49449 _5106 _5107) (@lem49448 _5106 _5107)). Qed.
Lemma lem49451 {_5106 _5107 : Type'} : (term146 _5106 _5107) = (term218 _5106 _5107).
Proof. exact (TRANS (@lem49367 _5106 _5107) (@lem49450 _5106 _5107)). Qed.
Lemma lem49452 {_5106 _5107 : Type'} : (term93 _5106 _5107) = (term218 _5106 _5107).
Proof. exact (TRANS (@lem49340 _5106 _5107) (@lem49451 _5106 _5107)). Qed.
Lemma lem49453 {_5106 _5107 : Type'} : (term69 _5106 _5107) = (term218 _5106 _5107).
Proof. exact (TRANS (@lem49143 _5106 _5107) (@lem49452 _5106 _5107)). Qed.
Lemma lem49454 {_5106 _5107 : Type'} : (term3 _5106 _5107) = (term218 _5106 _5107).
Proof. exact (TRANS (@lem49116 _5106 _5107) (@lem49453 _5106 _5107)). Qed.
Lemma lem49455 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : term218 _5106 _5107.
Proof. exact (EQ_MP (@lem49454 _5106 _5107) (@lem49051 _5106 _5107 h1)). Qed.
Lemma lem49456 {_5106 _5107 : Type'} (x : prod _5107 _5106) : ((term13 _5106 _5107 x) = x) = ((term13 _5106 _5107 x) = x).
Proof. exact (eq_refl ((term13 _5106 _5107 x) = x)). Qed.
Lemma lem49457 {_5106 _5107 : Type'} : (term14 _5106 _5107) = (term14 _5106 _5107).
Proof. exact (fun_ext (fun x : prod _5107 _5106 => @lem49456 _5106 _5107 x)). Qed.
Lemma lem49458 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem49467 {_5106 _5107 : Type'} : (term4 _5106 _5107) = (term4 _5106 _5107).
Proof. exact (MK_COMB (@lem49458 _5106 _5107) (@lem49457 _5106 _5107)). Qed.
Lemma lem49468 {_5106 _5107 : Type'} (h1 : term4 _5106 _5107) : term4 _5106 _5107.
Proof. exact (EQ_MP (@lem49467 _5106 _5107) (@lem49052 _5106 _5107 h1)). Qed.
Lemma lem49469 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (h1 : term216 _5106 _5107 P) : term216 _5106 _5107 P.
Proof. exact (h1). Qed.
Lemma lem49470 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) (h1 : term214 _5106 _5107 p1 P) : term214 _5106 _5107 p1 P.
Proof. exact (h1). Qed.
Lemma lem49471 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) (h1 : term212 _5106 _5107 p1 p2 P) : term212 _5106 _5107 p1 p2 P.
Proof. exact (h1). Qed.
Lemma lem49472 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term209 _5106 _5107 p1 p2 p P) : term209 _5106 _5107 p1 p2 p P.
Proof. exact (h1). Qed.
Lemma lem49485 {_5106 _5107 : Type'} (x : prod _5107 _5106) : ((term13 _5106 _5107 x) = x) = ((term13 _5106 _5107 x) = x).
Proof. exact (eq_refl ((term13 _5106 _5107 x) = x)). Qed.
Lemma lem49486 {_5106 _5107 : Type'} : (term14 _5106 _5107) = (term14 _5106 _5107).
Proof. exact (fun_ext (fun x : prod _5107 _5106 => @lem49485 _5106 _5107 x)). Qed.
Lemma lem49487 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem49488 {_5106 _5107 : Type'} : (term4 _5106 _5107) = (term4 _5106 _5107).
Proof. exact (MK_COMB (@lem49487 _5106 _5107) (@lem49486 _5106 _5107)). Qed.
Lemma lem49489 {_5106 _5107 : Type'} (h1 : term4 _5106 _5107) : term4 _5106 _5107.
Proof. exact (EQ_MP (@lem49488 _5106 _5107) (@lem49468 _5106 _5107 h1)). Qed.
Lemma lem49496 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term15 _5106 _5107 P p1 p2) = (term15 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term15 _5106 _5107 P p1 p2)). Qed.
Lemma lem49497 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term16 _5106 _5107 P p1) = (term16 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49496 _5106 _5107 P p1 p2)). Qed.
Lemma lem49498 {_5106 : Type'} : (@all _5106) = (@all _5106).
Proof. exact (eq_refl (@all _5106)). Qed.
Lemma lem49499 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term17 _5106 _5107 P p1) = (term17 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49498 _5106) (@lem49497 _5106 _5107 P p1)). Qed.
Lemma lem49500 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term18 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49499 _5106 _5107 P p1)). Qed.
Lemma lem49501 {_5107 : Type'} : (@all _5107) = (@all _5107).
Proof. exact (eq_refl (@all _5107)). Qed.
Lemma lem49502 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term19 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49501 _5107) (@lem49500 _5106 _5107 P)). Qed.
Lemma lem49509 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term138 _5106 _5107 P p) = (term138 _5106 _5107 P p).
Proof. exact (eq_refl (term138 _5106 _5107 P p)). Qed.
Lemma lem49510 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) : (term140 _5106 _5107 p P) = (term140 _5106 _5107 p P).
Proof. exact (MK_COMB (@lem49509 _5106 _5107 P p) (@lem49502 _5106 _5107 P)). Qed.
Lemma lem49519 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term39 _5106 _5107 P p1 p2) = (term39 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term39 _5106 _5107 P p1 p2)). Qed.
Lemma lem49522 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem49523 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term20 _5106 _5107 P) = (term20 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49522 _5106 _5107 P p)). Qed.
Lemma lem49524 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem49525 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term21 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49524 _5106 _5107) (@lem49523 _5106 _5107 P)). Qed.
Lemma lem49526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem49527 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term54 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49526) (@lem49525 _5106 _5107 P)). Qed.
Lemma lem49528 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term116 _5106 _5107 P p1 p2) = (term116 _5106 _5107 P p1 p2).
Proof. exact (MK_COMB (@lem49527 _5106 _5107 P) (@lem49519 _5106 _5107 P p1 p2)). Qed.
Lemma lem49529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem49530 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term191 _5106 _5107 P p1 p2) = (term191 _5106 _5107 P p1 p2).
Proof. exact (MK_COMB (@lem49529) (@lem49528 _5106 _5107 P p1 p2)). Qed.
Lemma lem49531 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) : (term209 _5106 _5107 p1 p2 p P) = (term209 _5106 _5107 p1 p2 p P).
Proof. exact (MK_COMB (@lem49530 _5106 _5107 P p1 p2) (@lem49510 _5106 _5107 p P)). Qed.
Lemma lem49532 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term209 _5106 _5107 p1 p2 p P) : term209 _5106 _5107 p1 p2 p P.
Proof. exact (EQ_MP (@lem49531 _5106 _5107 p1 p2 p P) (@lem49472 _5106 _5107 p1 p2 p P h1)). Qed.
Lemma lem49533 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term116 _5106 _5107 P p1 p2.
Proof. exact (h1). Qed.
Lemma lem49534 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term140 _5106 _5107 p P.
Proof. exact (h1). Qed.
Lemma lem49536 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term21 _5106 _5107 P.
Proof. exact (proj1 (@lem49533 _5106 _5107 P p1 p2 h1)). Qed.
Lemma lem49537 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term19 _5106 _5107 P.
Proof. exact (proj2 (@lem49534 _5106 _5107 p P h1)). Qed.
Lemma lem49547 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem49548 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term20 _5106 _5107 P) = (term20 _5106 _5107 P).
Proof. exact (fun_ext (fun p : prod _5107 _5106 => @lem49547 _5106 _5107 P p)). Qed.
Lemma lem49549 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem49551 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = (term21 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49549 _5106 _5107) (@lem49548 _5106 _5107 P)). Qed.
Lemma lem49552 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term21 _5106 _5107 P.
Proof. exact (EQ_MP (@lem49551 _5106 _5107 P) (@lem49536 _5106 _5107 P p1 p2 h1)). Qed.
Lemma lem49558 {_5106 _5107 : Type'} (x : prod _5107 _5106) : ((term13 _5106 _5107 x) = x) = ((term13 _5106 _5107 x) = x).
Proof. exact (eq_refl ((term13 _5106 _5107 x) = x)). Qed.
Lemma lem49559 {_5106 _5107 : Type'} : (term14 _5106 _5107) = (term14 _5106 _5107).
Proof. exact (fun_ext (fun x : prod _5107 _5106 => @lem49558 _5106 _5107 x)). Qed.
Lemma lem49560 {_5106 _5107 : Type'} : (@all (prod _5107 _5106)) = (@all (prod _5107 _5106)).
Proof. exact (eq_refl (@all (prod _5107 _5106))). Qed.
Lemma lem49562 {_5106 _5107 : Type'} : (term4 _5106 _5107) = (term4 _5106 _5107).
Proof. exact (MK_COMB (@lem49560 _5106 _5107) (@lem49559 _5106 _5107)). Qed.
Lemma lem49563 {_5106 _5107 : Type'} (h1 : term4 _5106 _5107) : term4 _5106 _5107.
Proof. exact (EQ_MP (@lem49562 _5106 _5107) (@lem49489 _5106 _5107 h1)). Qed.
Lemma lem49569 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term15 _5106 _5107 P p1 p2) = (term15 _5106 _5107 P p1 p2).
Proof. exact (eq_refl (term15 _5106 _5107 P p1 p2)). Qed.
Lemma lem49570 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term16 _5106 _5107 P p1) = (term16 _5106 _5107 P p1).
Proof. exact (fun_ext (fun p2 : _5106 => @lem49569 _5106 _5107 P p1 p2)). Qed.
Lemma lem49571 {_5106 : Type'} : (@all _5106) = (@all _5106).
Proof. exact (eq_refl (@all _5106)). Qed.
Lemma lem49572 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) : (term17 _5106 _5107 P p1) = (term17 _5106 _5107 P p1).
Proof. exact (MK_COMB (@lem49571 _5106) (@lem49570 _5106 _5107 P p1)). Qed.
Lemma lem49573 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term18 _5106 _5107 P) = (term18 _5106 _5107 P).
Proof. exact (fun_ext (fun p1 : _5107 => @lem49572 _5106 _5107 P p1)). Qed.
Lemma lem49574 {_5107 : Type'} : (@all _5107) = (@all _5107).
Proof. exact (eq_refl (@all _5107)). Qed.
Lemma lem49576 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term19 _5106 _5107 P).
Proof. exact (MK_COMB (@lem49574 _5107) (@lem49573 _5106 _5107 P)). Qed.
Lemma lem49577 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term19 _5106 _5107 P.
Proof. exact (EQ_MP (@lem49576 _5106 _5107 P) (@lem49537 _5106 _5107 p P h1)). Qed.
Lemma lem49581 {_5106 _5107 : Type'} (_1344 : prod _5107 _5106) (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term28 _5106 _5107 P _1344.
Proof. exact (@lem49552 _5106 _5107 P p1 p2 h1 _1344). Qed.
Lemma lem49582 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1344 : prod _5107 _5106) : (term28 _5106 _5107 P _1344) = (P _1344).
Proof. exact (eq_refl (term28 _5106 _5107 P _1344)). Qed.
Lemma lem49584 {_5106 _5107 : Type'} (_1345 : prod _5107 _5106) (h1 : term4 _5106 _5107) : term219 _5106 _5107 _1345.
Proof. exact (@lem49563 _5106 _5107 h1 _1345). Qed.
Lemma lem49585 {_5106 _5107 : Type'} (_1345 : prod _5107 _5106) : (term219 _5106 _5107 _1345) = ((term13 _5106 _5107 _1345) = _1345).
Proof. exact (eq_refl (term219 _5106 _5107 _1345)). Qed.
Lemma lem49587 {_5106 _5107 : Type'} (_1346 : _5107) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term45 _5106 _5107 P _1346.
Proof. exact (@lem49577 _5106 _5107 p P h1 _1346). Qed.
Lemma lem49588 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1346 : _5107) : (term45 _5106 _5107 P _1346) = (term17 _5106 _5107 P _1346).
Proof. exact (eq_refl (term45 _5106 _5107 P _1346)). Qed.
Lemma lem49589 {_5106 _5107 : Type'} (_1346 : _5107) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term17 _5106 _5107 P _1346.
Proof. exact (EQ_MP (@lem49588 _5106 _5107 P _1346) (@lem49587 _5106 _5107 _1346 p P h1)). Qed.
Lemma lem49590 {_5106 _5107 : Type'} (_1346 : _5107) (_1347 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term37 _5106 _5107 P _1346 _1347.
Proof. exact (@lem49589 _5106 _5107 _1346 p P h1 _1347). Qed.
Lemma lem49591 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1346 : _5107) (_1347 : _5106) : (term37 _5106 _5107 P _1346 _1347) = (term15 _5106 _5107 P _1346 _1347).
Proof. exact (eq_refl (term37 _5106 _5107 P _1346 _1347)). Qed.
Lemma lem49598 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term39 _5106 _5107 P p1 p2.
Proof. exact (proj2 (@lem49533 _5106 _5107 P p1 p2 h1)). Qed.
Lemma lem49602 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term30 _5106 _5107 P p.
Proof. exact (proj1 (@lem49534 _5106 _5107 p P h1)). Qed.
Lemma lem49655 {_5106 _5107 : Type'} (_1344 : prod _5107 _5106) (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : P _1344.
Proof. exact (EQ_MP (@lem49582 _5106 _5107 P _1344) (@lem49581 _5106 _5107 _1344 P p1 p2 h1)). Qed.
Lemma lem49656 {_5106 _5107 : Type'} (_1344 : prod _5107 _5106) (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : P _1344.
Proof. exact (@lem49655 _5106 _5107 _1344 P p1 p2 h1). Qed.
Lemma lem49657 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term15 _5106 _5107 P p1 p2.
Proof. exact (@lem49656 _5106 _5107 (@pair _5107 _5106 p1 p2) P p1 p2 h1). Qed.
Lemma lem49658 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term220 _5106 _5107 P p1 p2.
Proof. exact (fun h0 : term39 _5106 _5107 P p1 p2 => @lem49657 _5106 _5107 P p1 p2 h1). Qed.
Lemma lem49660 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem49661 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term220 _5106 _5107 P p1 p2) = (term15 _5106 _5107 P p1 p2).
Proof. exact (@lem49660 (term15 _5106 _5107 P p1 p2)). Qed.
Lemma lem49662 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term15 _5106 _5107 P p1 p2.
Proof. exact (EQ_MP (@lem49661 _5106 _5107 P p1 p2) (@lem49658 _5106 _5107 P p1 p2 h1)). Qed.
Lemma lem49665 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem49667 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) : (term39 _5106 _5107 P p1 p2) = (term222 _5106 _5107 P p1 p2).
Proof. exact (@lem49665 (term15 _5106 _5107 P p1 p2)). Qed.
Lemma lem49670 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term222 _5106 _5107 P p1 p2.
Proof. exact (EQ_MP (@lem49667 _5106 _5107 P p1 p2) (@lem49598 _5106 _5107 P p1 p2 h1)). Qed.
Lemma lem49673 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : False.
Proof. exact (@lem49670 _5106 _5107 P p1 p2 h1 (@lem49662 _5106 _5107 P p1 p2 h1)). Qed.
Lemma lem49674 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : term223.
Proof. exact (fun h0 : ~ False => @lem49673 _5106 _5107 P p1 p2 h1). Qed.
Lemma lem49676 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem49677 : term223 = False.
Proof. exact (@lem49676 False). Qed.
Lemma lem49678 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p1 : _5107) (p2 : _5106) (h1 : term116 _5106 _5107 P p1 p2) : False.
Proof. exact (EQ_MP (@lem49677) (@lem49674 _5106 _5107 P p1 p2 h1)). Qed.
Lemma lem49679 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem49680 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) (h1 : _1358 = _1359) : _1358 = _1359.
Proof. exact (h1). Qed.
Lemma lem49681 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) (h1 : _1358 = _1359) : (P _1358) = (P _1359).
Proof. exact (MK_COMB (@lem49679 _5106 _5107 P) (@lem49680 _5106 _5107 _1358 _1359 h1)). Qed.
Lemma lem49683 (b : Prop) (a : Prop) : term224 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem49684 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : term225 _5106 _5107 _1359 P _1358.
Proof. exact (@lem49683 (P _1359) (P _1358)). Qed.
Lemma lem49685 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) (h1 : _1358 = _1359) : term226 _5106 _5107 _1359 P _1358.
Proof. exact (@lem49684 _5106 _5107 _1359 P _1358 (@lem49681 _5106 _5107 P _1358 _1359 h1)). Qed.
Lemma lem49686 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : term227 _5106 _5107 _1359 P _1358.
Proof. exact (fun h0 : _1358 = _1359 => @lem49685 _5106 _5107 P _1358 _1359 h0). Qed.
Lemma lem49688 (a : Prop) (b : Prop) : (a -> b) = (term228 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem49689 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term227 _5106 _5107 _1359 P _1358) = (term229 _5106 _5107 _1359 P _1358).
Proof. exact (@lem49688 (_1358 = _1359) (term226 _5106 _5107 _1359 P _1358)). Qed.
Lemma lem49690 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : term229 _5106 _5107 _1359 P _1358.
Proof. exact (EQ_MP (@lem49689 _5106 _5107 _1359 P _1358) (@lem49686 _5106 _5107 _1359 P _1358)). Qed.
Lemma lem49729 {_5106 _5107 : Type'} (_1345 : prod _5107 _5106) (h1 : term4 _5106 _5107) : (term13 _5106 _5107 _1345) = _1345.
Proof. exact (EQ_MP (@lem49585 _5106 _5107 _1345) (@lem49584 _5106 _5107 _1345 h1)). Qed.
Lemma lem49730 {_5106 _5107 : Type'} (_1345 : prod _5107 _5106) (h1 : term4 _5106 _5107) : (term13 _5106 _5107 _1345) = _1345.
Proof. exact (@lem49729 _5106 _5107 _1345 h1). Qed.
Lemma lem49731 {_5106 _5107 : Type'} (p : prod _5107 _5106) (h1 : term4 _5106 _5107) : (term13 _5106 _5107 p) = p.
Proof. exact (@lem49730 _5106 _5107 p h1). Qed.
Lemma lem49732 {_5106 _5107 : Type'} (p : prod _5107 _5106) (h1 : term4 _5106 _5107) : term230 _5106 _5107 p.
Proof. exact (fun h0 : term231 _5106 _5107 p => @lem49731 _5106 _5107 p h1). Qed.
Lemma lem49734 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem49735 {_5106 _5107 : Type'} (p : prod _5107 _5106) : (term230 _5106 _5107 p) = ((term13 _5106 _5107 p) = p).
Proof. exact (@lem49734 ((term13 _5106 _5107 p) = p)). Qed.
Lemma lem49736 {_5106 _5107 : Type'} (p : prod _5107 _5106) (h1 : term4 _5106 _5107) : (term13 _5106 _5107 p) = p.
Proof. exact (EQ_MP (@lem49735 _5106 _5107 p) (@lem49732 _5106 _5107 p h1)). Qed.
Lemma lem49738 {_5106 _5107 : Type'} (_1346 : _5107) (_1347 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term15 _5106 _5107 P _1346 _1347.
Proof. exact (EQ_MP (@lem49591 _5106 _5107 P _1346 _1347) (@lem49590 _5106 _5107 _1346 _1347 p P h1)). Qed.
Lemma lem49739 {_5106 _5107 : Type'} (_1346 : _5107) (_1347 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term15 _5106 _5107 P _1346 _1347.
Proof. exact (@lem49738 _5106 _5107 _1346 _1347 p P h1). Qed.
Lemma lem49740 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term232 _5106 _5107 P p.
Proof. exact (@lem49739 _5106 _5107 (@fst _5107 _5106 p) (@snd _5107 _5106 p) p P h1). Qed.
Lemma lem49741 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term233 _5106 _5107 P p.
Proof. exact (fun h0 : term234 _5106 _5107 P p => @lem49740 _5106 _5107 p P h1). Qed.
Lemma lem49743 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem49744 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term233 _5106 _5107 P p) = (term232 _5106 _5107 P p).
Proof. exact (@lem49743 (term232 _5106 _5107 P p)). Qed.
Lemma lem49745 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term232 _5106 _5107 P p.
Proof. exact (EQ_MP (@lem49744 _5106 _5107 P p) (@lem49741 _5106 _5107 p P h1)). Qed.
Lemma lem49751 (q : Prop) (p : Prop) (r : Prop) : (term235 p q r) = (term235 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem49752 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term229 _5106 _5107 _1359 P _1358) = (term236 _5106 _5107 _1359 P _1358).
Proof. exact (@lem49751 (P _1359) (term237 _5106 _5107 _1358 _1359) (term30 _5106 _5107 P _1358)). Qed.
Lemma lem49766 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem49767 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term238 _5106 _5107 _1359 P _1358) = (term239 _5106 _5107 P _1358 _1359).
Proof. exact (@lem49766 (term30 _5106 _5107 P _1358) (term237 _5106 _5107 _1358 _1359)). Qed.
Lemma lem49775 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : (term240 _5106 _5107 P _1359) = (term240 _5106 _5107 P _1359).
Proof. exact (eq_refl (term240 _5106 _5107 P _1359)). Qed.
Lemma lem49776 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term236 _5106 _5107 _1359 P _1358) = (term241 _5106 _5107 P _1358 _1359).
Proof. exact (MK_COMB (@lem49775 _5106 _5107 P _1359) (@lem49767 _5106 _5107 P _1358 _1359)). Qed.
Lemma lem49787 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term229 _5106 _5107 _1359 P _1358) = (term241 _5106 _5107 P _1358 _1359).
Proof. exact (TRANS (@lem49752 _5106 _5107 _1359 P _1358) (@lem49776 _5106 _5107 P _1358 _1359)). Qed.
Lemma lem49788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem49789 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term242 _5106 _5107 _1359 P _1358) = (term243 _5106 _5107 P _1358 _1359).
Proof. exact (MK_COMB (@lem49788) (@lem49787 _5106 _5107 P _1358 _1359)). Qed.
Lemma lem49803 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem49804 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term238 _5106 _5107 _1359 P _1358) = (term239 _5106 _5107 P _1358 _1359).
Proof. exact (@lem49803 (term30 _5106 _5107 P _1358) (term237 _5106 _5107 _1358 _1359)). Qed.
Lemma lem49812 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : (term240 _5106 _5107 P _1359) = (term240 _5106 _5107 P _1359).
Proof. exact (eq_refl (term240 _5106 _5107 P _1359)). Qed.
Lemma lem49813 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term236 _5106 _5107 _1359 P _1358) = (term241 _5106 _5107 P _1358 _1359).
Proof. exact (MK_COMB (@lem49812 _5106 _5107 P _1359) (@lem49804 _5106 _5107 P _1358 _1359)). Qed.
Lemma lem49824 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : ((term229 _5106 _5107 _1359 P _1358) = (term236 _5106 _5107 _1359 P _1358)) = ((term241 _5106 _5107 P _1358 _1359) = (term241 _5106 _5107 P _1358 _1359)).
Proof. exact (MK_COMB (@lem49789 _5106 _5107 P _1358 _1359) (@lem49813 _5106 _5107 P _1358 _1359)). Qed.
Lemma lem49826 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem49827 (x : Prop) : (x = x) = True.
Proof. exact (@lem49826 Prop x). Qed.
Lemma lem49828 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : ((term241 _5106 _5107 P _1358 _1359) = (term241 _5106 _5107 P _1358 _1359)) = True.
Proof. exact (@lem49827 (term241 _5106 _5107 P _1358 _1359)). Qed.
Lemma lem49829 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : ((term229 _5106 _5107 _1359 P _1358) = (term236 _5106 _5107 _1359 P _1358)) = True.
Proof. exact (TRANS (@lem49824 _5106 _5107 P _1358 _1359) (@lem49828 _5106 _5107 P _1358 _1359)). Qed.
Lemma lem49830 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : True = ((term229 _5106 _5107 _1359 P _1358) = (term236 _5106 _5107 _1359 P _1358)).
Proof. exact (SYM (@lem49829 _5106 _5107 _1359 P _1358)). Qed.
Lemma lem49831 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term229 _5106 _5107 _1359 P _1358) = (term236 _5106 _5107 _1359 P _1358).
Proof. exact (EQ_MP (@lem49830 _5106 _5107 _1359 P _1358) (@lem0)). Qed.
Lemma lem49832 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : term236 _5106 _5107 _1359 P _1358.
Proof. exact (EQ_MP (@lem49831 _5106 _5107 _1359 P _1358) (@lem49690 _5106 _5107 _1359 P _1358)). Qed.
Lemma lem49834 (b : Prop) (a : Prop) : (a \/ b) = (term244 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem49835 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : (term236 _5106 _5107 _1359 P _1358) = (term245 _5106 _5107 _1358 P _1359).
Proof. exact (@lem49834 (term238 _5106 _5107 _1359 P _1358) (P _1359)). Qed.
Lemma lem49837 (a : Prop) (b : Prop) : (term246 a b) = (term247 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem49838 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term248 _5106 _5107 _1359 P _1358) = (term249 _5106 _5107 _1359 P _1358).
Proof. exact (@lem49837 (term237 _5106 _5107 _1358 _1359) (term30 _5106 _5107 P _1358)). Qed.
Lemma lem49840 (a : Prop) : (term250 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem49841 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term251 _5106 _5107 _1358 _1359) = (_1358 = _1359).
Proof. exact (@lem49840 (_1358 = _1359)). Qed.
Lemma lem49842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem49843 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (_1359 : prod _5107 _5106) : (term252 _5106 _5107 _1358 _1359) = (term253 _5106 _5107 _1358 _1359).
Proof. exact (MK_COMB (@lem49842) (@lem49841 _5106 _5107 _1358 _1359)). Qed.
Lemma lem49845 (a : Prop) : (term250 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem49846 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term254 _5106 _5107 P _1358) = (P _1358).
Proof. exact (@lem49845 (P _1358)). Qed.
Lemma lem49847 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term249 _5106 _5107 _1359 P _1358) = (term255 _5106 _5107 _1359 P _1358).
Proof. exact (MK_COMB (@lem49843 _5106 _5107 _1358 _1359) (@lem49846 _5106 _5107 P _1358)). Qed.
Lemma lem49848 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term248 _5106 _5107 _1359 P _1358) = (term255 _5106 _5107 _1359 P _1358).
Proof. exact (TRANS (@lem49838 _5106 _5107 _1359 P _1358) (@lem49847 _5106 _5107 _1359 P _1358)). Qed.
Lemma lem49849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem49850 {_5106 _5107 : Type'} (_1359 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1358 : prod _5107 _5106) : (term256 _5106 _5107 _1359 P _1358) = (term257 _5106 _5107 _1359 P _1358).
Proof. exact (MK_COMB (@lem49849) (@lem49848 _5106 _5107 _1359 P _1358)). Qed.
Lemma lem49851 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : (P _1359) = (P _1359).
Proof. exact (eq_refl (P _1359)). Qed.
Lemma lem49852 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : (term245 _5106 _5107 _1358 P _1359) = (term258 _5106 _5107 _1358 P _1359).
Proof. exact (MK_COMB (@lem49850 _5106 _5107 _1359 P _1358) (@lem49851 _5106 _5107 P _1359)). Qed.
Lemma lem49853 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : (term236 _5106 _5107 _1359 P _1358) = (term258 _5106 _5107 _1358 P _1359).
Proof. exact (TRANS (@lem49835 _5106 _5107 _1358 P _1359) (@lem49852 _5106 _5107 _1358 P _1359)). Qed.
Lemma lem49855 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : term259 _5106 _5107 P p.
Proof. exact (conj (@lem49736 _5106 _5107 p h1) (@lem49745 _5106 _5107 p P h2)). Qed.
Lemma lem49857 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : term258 _5106 _5107 _1358 P _1359.
Proof. exact (EQ_MP (@lem49853 _5106 _5107 _1358 P _1359) (@lem49832 _5106 _5107 _1359 P _1358)). Qed.
Lemma lem49858 {_5106 _5107 : Type'} (_1358 : prod _5107 _5106) (P : type1223 _5106 _5107) (_1359 : prod _5107 _5106) : term258 _5106 _5107 _1358 P _1359.
Proof. exact (@lem49857 _5106 _5107 _1358 P _1359). Qed.
Lemma lem49859 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : term260 _5106 _5107 P p.
Proof. exact (@lem49858 _5106 _5107 (term13 _5106 _5107 p) P p). Qed.
Lemma lem49862 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : P p.
Proof. exact (@lem49859 _5106 _5107 P p (@lem49855 _5106 _5107 p P h1 h2)). Qed.
Lemma lem49863 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : term261 _5106 _5107 P p.
Proof. exact (fun h0 : term30 _5106 _5107 P p => @lem49862 _5106 _5107 p P h1 h2). Qed.
Lemma lem49865 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem49866 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term261 _5106 _5107 P p) = (P p).
Proof. exact (@lem49865 (P p)). Qed.
Lemma lem49867 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : P p.
Proof. exact (EQ_MP (@lem49866 _5106 _5107 P p) (@lem49863 _5106 _5107 p P h1 h2)). Qed.
Lemma lem49870 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem49872 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (p : prod _5107 _5106) : (term30 _5106 _5107 P p) = (term262 _5106 _5107 P p).
Proof. exact (@lem49870 (P p)). Qed.
Lemma lem49875 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term140 _5106 _5107 p P) : term262 _5106 _5107 P p.
Proof. exact (EQ_MP (@lem49872 _5106 _5107 P p) (@lem49602 _5106 _5107 p P h1)). Qed.
Lemma lem49878 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : False.
Proof. exact (@lem49875 _5106 _5107 p P h2 (@lem49867 _5106 _5107 p P h1 h2)). Qed.
Lemma lem49879 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : term223.
Proof. exact (fun h0 : ~ False => @lem49878 _5106 _5107 p P h1 h2). Qed.
Lemma lem49881 (p : Prop) : (term221 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem49882 : term223 = False.
Proof. exact (@lem49881 False). Qed.
Lemma lem49883 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : False.
Proof. exact (EQ_MP (@lem49882) (@lem49879 _5106 _5107 p P h1 h2)). Qed.
Lemma lem49884 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : (term4 _5106 _5107) = False.
Proof. exact (prop_ext (fun h3 : term4 _5106 _5107 => @lem49883 _5106 _5107 p P h1 h2) (fun h3 : False => @lem49563 _5106 _5107 h1)). Qed.
Lemma lem49885 {_5106 _5107 : Type'} (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term140 _5106 _5107 p P) : False.
Proof. exact (EQ_MP (@lem49884 _5106 _5107 p P h1 h2) (@lem49563 _5106 _5107 h1)). Qed.
Lemma lem49886 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term209 _5106 _5107 p1 p2 p P) : False.
Proof. exact (or_elim (@lem49532 _5106 _5107 p1 p2 p P h2) (fun h0 : term116 _5106 _5107 P p1 p2 => @lem49678 _5106 _5107 P p1 p2 h0) (fun h0 : term140 _5106 _5107 p P => @lem49885 _5106 _5107 p P h1 h0)). Qed.
Lemma lem49887 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term209 _5106 _5107 p1 p2 p P) : (term209 _5106 _5107 p1 p2 p P) = False.
Proof. exact (prop_ext (fun h3 : term209 _5106 _5107 p1 p2 p P => @lem49886 _5106 _5107 p1 p2 p P h1 h2) (fun h3 : False => @lem49532 _5106 _5107 p1 p2 p P h2)). Qed.
Lemma lem49888 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term209 _5106 _5107 p1 p2 p P) : False.
Proof. exact (EQ_MP (@lem49887 _5106 _5107 p1 p2 p P h1 h2) (@lem49532 _5106 _5107 p1 p2 p P h2)). Qed.
Lemma lem49889 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term209 _5106 _5107 p1 p2 p P) : (term4 _5106 _5107) = False.
Proof. exact (prop_ext (fun h3 : term4 _5106 _5107 => @lem49888 _5106 _5107 p1 p2 p P h1 h2) (fun h3 : False => @lem49489 _5106 _5107 h1)). Qed.
Lemma lem49890 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (p : prod _5107 _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term209 _5106 _5107 p1 p2 p P) : False.
Proof. exact (EQ_MP (@lem49889 _5106 _5107 p1 p2 p P h1 h2) (@lem49489 _5106 _5107 h1)). Qed.
Lemma lem49891 {_5106 _5107 : Type'} (p1 : _5107) (p2 : _5106) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term212 _5106 _5107 p1 p2 P) : False.
Proof. exact (ex_elim (@lem49471 _5106 _5107 p1 p2 P h2) (fun p : prod _5107 _5106 => fun h0 : term211 _5106 _5107 p1 p2 P p => @lem49890 _5106 _5107 p1 p2 p P h1 h0)). Qed.
Lemma lem49892 {_5106 _5107 : Type'} (p1 : _5107) (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term214 _5106 _5107 p1 P) : False.
Proof. exact (ex_elim (@lem49470 _5106 _5107 p1 P h2) (fun p2 : _5106 => fun h0 : term213 _5106 _5107 p1 P p2 => @lem49891 _5106 _5107 p1 p2 P h1 h0)). Qed.
Lemma lem49893 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) (h1 : term4 _5106 _5107) (h2 : term216 _5106 _5107 P) : False.
Proof. exact (ex_elim (@lem49469 _5106 _5107 P h2) (fun p1 : _5107 => fun h0 : term215 _5106 _5107 P p1 => @lem49892 _5106 _5107 p1 P h1 h0)). Qed.
Lemma lem49894 {_5106 _5107 : Type'} (h1 : term4 _5106 _5107) (h2 : term3 _5106 _5107) : False.
Proof. exact (ex_elim (@lem49455 _5106 _5107 h2) (fun P : type1223 _5106 _5107 => fun h0 : term217 _5106 _5107 P => @lem49893 _5106 _5107 P h1 h0)). Qed.
Lemma lem49895 {_5106 _5107 : Type'} (h1 : term4 _5106 _5107) (h2 : term3 _5106 _5107) : (term4 _5106 _5107) = False.
Proof. exact (prop_ext (fun h3 : term4 _5106 _5107 => @lem49894 _5106 _5107 h1 h2) (fun h3 : False => @lem49468 _5106 _5107 h1)). Qed.
Lemma lem49896 {_5106 _5107 : Type'} (h1 : term4 _5106 _5107) (h2 : term3 _5106 _5107) : False.
Proof. exact (EQ_MP (@lem49895 _5106 _5107 h1 h2) (@lem49468 _5106 _5107 h1)). Qed.
Lemma lem49897 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : term9 _5106 _5107.
Proof. exact (fun h0 : term4 _5106 _5107 => @lem49896 _5106 _5107 h0 h1). Qed.
Lemma lem49898 {_5106 _5107 : Type'} : (term9 _5106 _5107) = (term10 _5106 _5107).
Proof. exact (@lem69 (term4 _5106 _5107)). Qed.
Lemma lem49899 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : term10 _5106 _5107.
Proof. exact (EQ_MP (@lem49898 _5106 _5107) (@lem49897 _5106 _5107 h1)). Qed.
Lemma lem49900 {_5106 _5107 : Type'} : term12 _5106 _5107.
Proof. exact (fun h0 : term3 _5106 _5107 => @lem49899 _5106 _5107 h0). Qed.
Lemma lem49901 {_5106 _5107 : Type'} : term5 _5106 _5107.
Proof. exact (EQ_MP (@lem49050 _5106 _5107) (@lem49900 _5106 _5107)). Qed.
Lemma lem49903 {_5106 _5107 : Type'} : term5 _5106 _5107.
Proof. exact (@lem48953 _5106 _5107 (@lem49901 _5106 _5107)). Qed.
Lemma lem49904 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : term9 _5106 _5107.
Proof. exact (@lem49903 _5106 _5107 (@lem48936 _5106 _5107 h1)). Qed.
Lemma lem49905 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : False.
Proof. exact (@lem49904 _5106 _5107 h1 (@lem48937 _5106 _5107)). Qed.
Lemma lem49906 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : (term3 _5106 _5107) = False.
Proof. exact (prop_ext (fun h2 : term3 _5106 _5107 => @lem49905 _5106 _5107 h1) (fun h2 : False => @lem48936 _5106 _5107 h1)). Qed.
Lemma lem49907 {_5106 _5107 : Type'} (h1 : term3 _5106 _5107) : False.
Proof. exact (EQ_MP (@lem49906 _5106 _5107 h1) (@lem48936 _5106 _5107 h1)). Qed.
Lemma lem49908 {_5106 _5107 : Type'} : term2 _5106 _5107.
Proof. exact (fun h0 : term3 _5106 _5107 => @lem49907 _5106 _5107 h0). Qed.
Lemma lem49909 {_5106 _5107 : Type'} : term1 _5106 _5107.
Proof. exact (EQ_MP (@lem48935 _5106 _5107) (@lem49908 _5106 _5107)). Qed.
