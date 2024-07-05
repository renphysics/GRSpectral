(* ::Package:: *)

(*
spNDSolve v0.2, by Jie Ren, 2024/7/6
https://github.com/renphysics/spNDSolve
A Mathematica package for solving PDEs by the pseudospectral method
*)


eqProcess::usage = "eqProcess[func_,eq_,bdyprerepl_List,s_String:\"\",opt:OptionsPattern[]]";
spNDSolve::usage = "spNDSolve[{x_, y_}, {fx_, fy_}, {nxGrid0_, nyGrid0_}, {par___}, s_String:\"\", OptionsPattern[]]";
spNIntegrate::usage = "spNIntegrate[x, fx, nxGrid0, expr, \"s\", rules]. It calls cheb[x, fx, nxGrid0, s, rules] and produces global variables \"lhs\" and \"rhs\" with surfix \"s\". e.g., spNIntegrate[x, linearMap[{1, 2}], 20, Sin[x], \"s\"]\[LeftDoubleBracket]-1\[RightDoubleBracket] does the work of NIntegrate[Sin[x], {x, 1, 2}]";


CircleTimes=KroneckerProduct;


CirclePlus[x__]:=ArrayFlatten@ReleaseHold@DiagonalMatrix[Hold/@{x}];


SetAttributes[Diamond,{HoldAll,Listable}];
Diamond[x__]:=toHeldExpression@StringJoin[Sequence@@toString[{x}]];


DotEqual[a_HoldForm,b_]:=(a/.hold[lft_]:>hold[lft=b])//ReleaseHold;
DotEqual[a_List,b_List]:=MapThread[DotEqual,{a,b}];


Off[LinearSolve::luc];


SubStar=Replace[Flatten[{#}],(y_/;Head[y]=!=Equal):>(y==0),1]&;


SuperStar=Replace[Flatten[{#1}],y_/;Head[y]===Equal:>y[[1]]-y[[2]],1]&;


Attributes[Vee]={HoldAll,Listable};
Vee[x__]:=ToExpression[StringJoin[Sequence@@toString[{x}]]];


addTo[a_List,b_List]:=MapThread[AddTo,{a,b}];


arrayDrop[m_,ind_]:=m[[##]]&@@(Complement[Range@#,Flatten[{ind}]]&/@Dimensions[m]);


SetAttributes[auxReplace,HoldAll];
auxReplace[x_]:={x\[Diamond]"aux1"\[Diamond]"="\[Diamond]x\[Diamond]"aux2"\[Diamond]"="\[Diamond]x\[Diamond]"aux12"\[Diamond]"="\[Diamond]x,x\[Diamond]"aux1"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]",x\[Diamond]"aux2"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]",x\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind1\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind1rep\[RightDoubleBracket]",x\[Diamond]"aux12"\[Diamond]"\[LeftDoubleBracket]ind2\[RightDoubleBracket]"\[Diamond]"="\[Diamond]x\[Diamond]"\[LeftDoubleBracket]ind2rep\[RightDoubleBracket]"}//release;


SetAttributes[bdyCondition,HoldRest];
Options[bdyCondition]={timesQ->False};
bdyCondition[{flist_,reflist___},bdyprerepl_,s_String:"",opt:OptionsPattern[]]:=Module[{bdyprereplh,bdyloc0,bdylist0,bdymat0,bdyind0,bdylinearize},
bdyprereplh=hold[bdyprerepl];
bdyloc0=bdyprereplh[[1,All,1]];
bdylist0=Map[toString,Replace[bdyprereplh,{_,b_}:>b,{2}]]//release;
bdymat0=StringReplace[bdylist0,"list"->"mat"];
bdyind0=Table["bdyind"<>s<>ToString[i],{i,Length[bdylist0]}];
Clear[Evaluate[bdyind0]];
calcbdyind\[Diamond]s\[DotEqual](calcIndex[{ToExpression[bdyind0],bdyloc0}\[Transpose],s]//unmap);
bdyrepl\[Diamond]s\[DotEqual]unmap@toHeldExpression[{bdyind0,bdylist0,bdymat0}\[Transpose]];
bdylinearize=Join[{ToExpression[bdylist0]},{bdylist0},{bdymat0}]\[Transpose];
eqLinearize[{flist,reflist},bdylinearize,s,opt];];
bdyCondition[{flist_,reflist___},bdyprerepl_,\[Lambda]_,s_String:"",opt:OptionsPattern[]]:=Module[{bdyprereplh,bdyloc0,bdylist0,bdymat0,bdyind0,bdyeigen},
bdyprereplh=hold[bdyprerepl];
bdyloc0=bdyprereplh[[1,All,1]];
bdylist0=Map[toString,Replace[bdyprereplh,{_,b_}:>b,{2}]]//release;
bdymat0=StringReplace[bdylist0,"list"->"mat"];
bdyind0=Table["bdyind"<>s<>ToString[i],{i,Length[bdylist0]}];
Clear[Evaluate[bdyind0]];
calcbdyind\[Diamond]s\[DotEqual](calcIndex[{ToExpression[bdyind0],bdyloc0}\[Transpose],s]//unmap);
bdyrepl\[Diamond]s\[DotEqual]unmap@toHeldExpression[{bdyind0,bdymat0}\[Transpose]];
bdyeigen=Join[{ToExpression[bdylist0]},{bdymat0}]\[Transpose];
eqEigen[{flist,reflist},bdyeigen,\[Lambda],s,opt];];


bdyIndex[m_Integer,{n_Integer},s_String:""]:=Which[dimPDE===1,
Which[m==1,{(n-1) dimGrid\[Vee]s+1},
m==2,{n dimGrid\[Vee]s}],
dimPDE===2,
Which[m==1,Flatten[(n-1) dimGrid\[Vee]s+Table[i,{i,1,nyGrid\[Vee]s+1}]],
m==2,Flatten[(n-1) dimGrid\[Vee]s+Table[i,{i,nxGrid\[Vee]s(nyGrid\[Vee]s+1)+1,nxGrid\[Vee]s(nyGrid\[Vee]s+1)+nyGrid\[Vee]s+1}]],
m==3,Flatten[(n-1) dimGrid\[Vee]s+Table[i(nyGrid\[Vee]s+1)+1,{i,0,nxGrid\[Vee]s}]],
m==4,Flatten[(n-1) dimGrid\[Vee]s+Table[i(nyGrid\[Vee]s+1)+nyGrid\[Vee]s+1,{i,0,nxGrid\[Vee]s}]],
m==13,{(n-1) dimGrid\[Vee]s+1},
m==14,{(n-1) dimGrid\[Vee]s+nyGrid\[Vee]s+1},
m==23,{(n-1) dimGrid\[Vee]s+nxGrid\[Vee]s(nyGrid\[Vee]s+1)+1},
m==24,{n dimGrid\[Vee]s}]];
bdyIndex[m_Integer,{n__Integer},s_String:""]:=bdyIndex[m,{#},s]&/@{n}//Flatten;
bdyIndex[m_List,{n__Integer},s_String:""]:=bdyIndex[#,{n},s]&/@m;
bdyIndex[m_Integer,nEq_Integer,s_String:""]:=Table[bdyIndex[m,{n},s],{n,1,nEq}]//Flatten;
bdyIndex[m_List,nEq_Integer,s_String:""]:=bdyIndex[#,nEq,s]&/@m;
bdyIndex[m_,s_String:""]:=bdyIndex[m,nEq\[Vee]s,s];
bdyIndex[m_,nEq_Integer,"c",s_String:""]:=Complement[Range[dimGrid\[Vee]s nEq],Flatten@bdyIndex[m,nEq,s]];


SetAttributes[bdyLinearize,HoldRest];
Options[bdyLinearize]={timesQ->False};
bdyLinearize[{flist_,reflist___},bdyprerepl_,s_String:"",opt:OptionsPattern[]]:=Module[{bdyprereplh,strtemp,listtemp,mattemp,bdylinearize},
bdyprereplh=hold[bdyprerepl];
strtemp=Map[toString,bdyprereplh,{3}]//release;
listtemp=strtemp[[;;,2]];
mattemp=StringReplace[listtemp,"list"->"mat"];
bdyrepl\[Diamond]s\[DotEqual]unmap@toHeldExpression[Join[strtemp\[Transpose],{mattemp}]\[Transpose]];
bdylinearize=Join[{ToExpression[listtemp]},{listtemp},{mattemp}]\[Transpose];
eqLinearize[{flist,reflist},bdylinearize,s,opt];];


bdyReplace[bdyind_List,bdylist_List,bdymat_List,s_String:""]:={lhs\[Diamond]s[[bdyind]]\[DotEqual]ArrayFlatten[bdymat][[bdyind]],rhs\[Diamond]s[[bdyind]]\[DotEqual]-Flatten[bdylist][[bdyind]]};
bdyReplace[bdyind_List,bdymat_List,s_String:""]:={lhs\[Diamond]s[[All,bdyind]]\[DotEqual](ArrayFlatten/@bdymat)[[All,bdyind]]};
bdyReplace[bdyrepl_List,s_String:""]:=bdyReplace[Sequence@@#,s]&/@bdyrepl;


byteCount=memoryForm@ByteCount[#]&;


calcDeriv[f_[x_?AtomQ]]:={f\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f};
calcDeriv[f_[x_?AtomQ,y_?AtomQ]]:={f\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]y\[Diamond]"."\[Diamond]f};
calcDeriv[f_[x_?AtomQ,y_?AtomQ,z_?AtomQ]]:={f\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]z\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]z\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]z\[Diamond]"."\[Diamond]f,f\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f,f\[Diamond]y\[Diamond]y\[Diamond]"="\[Diamond]"d"\[Diamond]y\[Diamond]y\[Diamond]"."\[Diamond]f,f\[Diamond]z\[Diamond]z\[Diamond]"="\[Diamond]"d"\[Diamond]z\[Diamond]z\[Diamond]"."\[Diamond]f};
calcDeriv[flist_List]:=calcDeriv[#//Flatten]&/@flist//Flatten;


calcIndex[{bdyind_?AtomQ,{bdyloc__}},s_String:""]:=HoldForm[bdyind=index[bdyloc]];
calcIndex[{bdyind_?AtomQ,bdyloc_},s_String:""]:=HoldForm[bdyind=index[bdyloc,nEq\[Vee]s]];
calcIndex[{indloc__List},s_String:""]:=calcIndex[#,s]&/@{indloc};


Options[calcInterp]={derivQ->False};
calcInterp[f_[x_?AtomQ],suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f,f\[Diamond]x,f\[Diamond]x\[Diamond]x}//ReleaseHold;
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]x\[Diamond]x}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=#2[x]]&,{lft,rt}],MapThread[hold[#1=#2[x]]&,{{lft[[1]]},{rt[[1]]}}]]];
calcInterp[f_[x_?AtomQ,y_?AtomQ],suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f,f\[Diamond]x,f\[Diamond]y,f\[Diamond]x\[Diamond]y,f\[Diamond]x\[Diamond]x,f\[Diamond]y\[Diamond]y}//ReleaseHold;
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]x,f\[Diamond]suf\[Diamond]y\[Diamond]y}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=#2[x,y]]&,{lft,rt}],MapThread[hold[#1=#2[x,y]]&,{{lft[[1]]},{rt[[1]]}}]]];
calcInterp[flist_List,suf_String:"f",opt:OptionsPattern[]]:=calcInterp[#//Flatten,suf,opt]&/@flist//Flatten;


changeOptions[f_,a_->b_]:=If[MemberQ[f,a->x_],f/.(a->x_)->(a->b),Head[f][Sequence@@f,a->b]];
changeOptions[f_,rule__Rule]:=Fold[changeOptions,f,{rule}];


SetAttributes[cheb,HoldFirst];
Options[cheb]={minPrec->0,"D"->False};
cheb[x_/;AtomQ@Unevaluated[x],fx_Function,nxGrid0_,s_String:"",OptionsPattern[]]:=Block[{xtemp,fdx,fdxCheb,fdxCheb2,ind1,ind2,ind1rep,ind2rep},
dimPDE=1;
{nxGrid\[Diamond]s,xCheb\[Diamond]s,dxCheb\[Diamond]s}\[DotEqual]chebx[nxGrid0,OptionValue[minPrec]];
dimGrid\[Diamond]s\[DotEqual](nxGrid\[Vee]s+1);
If[AtomQ[nxGrid0]==False&&nxGrid0[[-1]]==="periodic",xPeriod\[Diamond]s\[DotEqual]fx[2\[Pi]];,Clear[Evaluate["xPeriod"<>s]];];
x=fx[xCheb\[Vee]s]//Quiet;
fdx[xtemp_]=1/fx'[xtemp]//Simplify;
fdxCheb=fdx[xCheb\[Vee]s]dxCheb\[Vee]s; fdxCheb2=fdxCheb . fdxCheb;
{"d"\[Diamond]x\[Diamond]"="\[Diamond]fdxCheb,"d"\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond]fdxCheb2}//release;

id\[Diamond]s\[DotEqual]IdentityMatrix[nxGrid\[Vee]s+1];
zero\[Diamond]s\[DotEqual]0id\[Vee]s;
one\[Diamond]s\[DotEqual]Table[1,{dimGrid\[Vee]s}];

If[OptionValue["D"]=!=False,{x\[Diamond]"","d"\[Diamond]x,"d"\[Diamond]x\[Diamond]x,id\[Diamond]s,zero\[Diamond]s,one\[Diamond]s}\[DotEqual](arrayDrop[#,bdyIndex[OptionValue["D"],1]]&/@{x,"d"\[Vee]x,"d"\[Vee]x\[Vee]x,id\[Vee]s,zero\[Vee]s,one\[Vee]s})];

ind1=bdyIndex[1,1,s];
ind2=bdyIndex[2,1,s];
ind1rep=ind1+1;
ind2rep=ind2-1;
auxReplace[x];];
cheb[x_/;AtomQ@Unevaluated[x],nxGrid0_,s_String:"",opt:OptionsPattern[]]:=cheb[x,#&,nxGrid0,s,opt];

cheb[{x_,y_},{fx_Function,fy_Function},{nxGrid0_,nyGrid0_},s_String:"",OptionsPattern[]]:=Block[{xtemp,ytemp,fdx,fdy,fdxCheb,fdxCheb2,fdyCheb,fdyCheb2,idx,idy,ind1,ind2,ind1rep,ind2rep},
dimPDE=2;
{nxGrid\[Diamond]s,xCheb\[Diamond]s,dxCheb\[Diamond]s}\[DotEqual]chebx[nxGrid0,OptionValue[minPrec]];
{nyGrid\[Diamond]s,yCheb\[Diamond]s,dyCheb\[Diamond]s}\[DotEqual]chebx[nyGrid0,OptionValue[minPrec]];
dimGrid\[Diamond]s\[DotEqual](nxGrid\[Vee]s+1)(nyGrid\[Vee]s+1);
If[AtomQ[nxGrid0]==False&&nxGrid0[[-1]]==="periodic",xPeriod\[Diamond]s\[DotEqual]fx[2\[Pi]];,Clear[Evaluate["xPeriod"<>s]];];
If[AtomQ[nyGrid0]==False&&nyGrid0[[-1]]==="periodic",yPeriod\[Diamond]s\[DotEqual]fy[2\[Pi]];,Clear[Evaluate["yPeriod"<>s]];];
idx=IdentityMatrix[nxGrid\[Vee]s+1];
idy=IdentityMatrix[nyGrid\[Vee]s+1];
x=Flatten[fx[xCheb\[Vee]s]\[CircleTimes]Table[1,{nyGrid\[Vee]s+1}]]//Quiet;
y=Flatten[Table[1,{nxGrid\[Vee]s+1}]\[CircleTimes]fy[yCheb\[Vee]s]]//Quiet;
fdx[xtemp_]=1/fx'[xtemp]//Simplify;
fdy[ytemp_]=1/fy'[ytemp]//Simplify;
fdxCheb=fdx[xCheb\[Vee]s]dxCheb\[Vee]s; fdxCheb2=fdxCheb . fdxCheb;
fdyCheb=fdy[yCheb\[Vee]s]dyCheb\[Vee]s; fdyCheb2=fdyCheb . fdyCheb;
{"d"\[Diamond]x\[Diamond]"="\[Diamond](fdxCheb\[CircleTimes]idy),"d"\[Diamond]y\[Diamond]"="\[Diamond](idx\[CircleTimes]fdyCheb),"d"\[Diamond]x\[Diamond]y\[Diamond]"="\[Diamond](fdxCheb\[CircleTimes]fdyCheb),"d"\[Diamond]x\[Diamond]x\[Diamond]"="\[Diamond](fdxCheb2\[CircleTimes]idy),"d"\[Diamond]y\[Diamond]y\[Diamond]"="\[Diamond](idx\[CircleTimes]fdyCheb2)}//ReleaseHold;

id\[Diamond]s\[DotEqual]idx\[CircleTimes]idy;
zero\[Diamond]s\[DotEqual]0id\[Vee]s;
one\[Diamond]s\[DotEqual]Table[1,{dimGrid\[Vee]s}];

If[OptionValue["D"]=!=False,{x\[Diamond]"",y\[Diamond]"","d"\[Diamond]x,"d"\[Diamond]y,"d"\[Diamond]x\[Diamond]y,"d"\[Diamond]x\[Diamond]x,"d"\[Diamond]y\[Diamond]y,id\[Diamond]s,zero\[Diamond]s,one\[Diamond]s}\[DotEqual](arrayDrop[#,bdyIndex[OptionValue["D"],1]]&/@{x,y,"d"\[Vee]x,"d"\[Vee]y,"d"\[Vee]x\[Vee]y,"d"\[Vee]x\[Vee]x,"d"\[Vee]y\[Vee]y,id\[Vee]s,zero\[Vee]s,one\[Vee]s})];

ind1=bdyIndex[1,1,s];
ind2=bdyIndex[2,1,s];
ind1rep=ind1+nyGrid\[Vee]s+1;
ind2rep=ind2-nyGrid\[Vee]s-1;
auxReplace[x];
ind1=bdyIndex[3,1,s];
ind2=bdyIndex[4,1,s];
ind1rep=ind1+1;
ind2rep=ind2-1;
auxReplace[y];];
cheb[{x_,y_},{nxGrid0_,nyGrid0_},s_String:"",opt:OptionsPattern[]]:=cheb[{x,y},{#&,#&},{nxGrid0,nyGrid0},s,opt];


chebx[nxGrid0_,minPrec_:0]:=Module[{nxGrid,xCheb,dxCheb},
If[minPrec!=0,
prec=$MinPrecision=minPrec;,
$MinPrecision=0;
prec=MachinePrecision;];
If[AtomQ[nxGrid0]==True,
nxGrid=nxGrid0;
xCheb=-N[Table[Cos[(j \[Pi])/nxGrid],{j,0,nxGrid}],prec];
If[$useNDSolve===True,
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,DifferenceOrder->"Pseudospectral"]["DifferentiationMatrix"];,
dxCheb=N[Table[If[i!=j,(-1)^(i+j)/(xCheb[[i]]-xCheb[[j]]) If[i==1||i==nxGrid+1,2,1]/If[j==1||j==nxGrid+1,2,1],0],{i,nxGrid+1},{j,nxGrid+1}],prec];
dxCheb=dxCheb-DiagonalMatrix[Plus@@@dxCheb];];,

nxGrid=nxGrid0[[1]];
Which[nxGrid0[[-1]]==="cheb",
xCheb=-N[Table[Cos[(j \[Pi])/nxGrid],{j,0,nxGrid}],prec];
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,DifferenceOrder->nxGrid0[[2]]]["DifferentiationMatrix"];,

nxGrid0[[-1]]==="uniform"||Head[nxGrid0[[-1]]]===Integer,
xCheb=-N[Table[(nxGrid-2j)/nxGrid,{j,0,nxGrid}],prec];
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,DifferenceOrder->nxGrid0[[2]]]["DifferentiationMatrix"];,

nxGrid0[[-1]]==="periodic",
nxGrid+=1;
xCheb=N[Table[(2\[Pi] j)/nxGrid,{j,0,nxGrid}],prec];
If[$useNDSolve===True,
dxCheb=NDSolve`FiniteDifferenceDerivative[1,xCheb,PeriodicInterpolation->True,DifferenceOrder->"Pseudospectral"]["DifferentiationMatrix"];,
dxCheb=N[Table[If[i!=j,(-1)^(i+j)/2 If[EvenQ[nxGrid],Cot,Csc][(xCheb[[i]]-xCheb[[j]])/2],0],{i,nxGrid},{j,nxGrid}],prec];
dxCheb=dxCheb-DiagonalMatrix[Plus@@@dxCheb];];
xCheb=xCheb[[1;;-2]]; nxGrid-=1;];];
{nxGrid,xCheb,dxCheb}];


checkSol[eq_,sol_,simp_:simplify]:=eq/.Head@getFunc[eq][[1]]->Function[Evaluate[getVar[eq][[1]]],Evaluate[sol]]//simp;


SetAttributes[clear,HoldAll];
clear[x_]:=(Clear[x];x);


clearAll:=ClearAll[Evaluate[$Context<>"*"]];
clearAll::usage="clearAll clears all values, definitions, attributes, messages and defaults associated with symbols in the current context";


closePoints[lis1_?VectorQ,lis2_?VectorQ,cutoff_:10^-2]:=Select[Flatten[Table[{w,Abs[z-w]},{z,lis1},{w,lis2}],1],#[[2]]<cutoff&];
closePoints[{lis1_?VectorQ,lis2_?VectorQ},cutoff_:10^-2]:=closePoints[lis1,lis2,cutoff];


collect[eq_,vars_List,trans_:Simplify]:=Collect[eq/Coefficient[eq,vars[[1]]],vars,trans];


cond[mat_?MatrixQ]:=LinearSolve[mat]["ConditionNumber"];


cond2[mat_?MatrixQ]:=Divide@@Table[SingularValueList[mat,k,Tolerance->0][[1]],{k,{1,-1}}];


SetAttributes[continue,HoldAll];
continue[expr_,plists__List]:=Module[{lis,nlis,lismin,lismax,listab,i},
lis=range/@(List@@MapAt[clear,Hold[plists],{All,1}]);
nlis=Length[lis];
lismin=MapAt[{#[[1]]}&,lis,{All,2}];
lismax=MapAt[{#[[-1]]}&,lis,{All,2}];
lis[[1;;-2,2,-1]]=Nothing;
listab=Table[{Sequence@@lismax[[;;i-1]],lis[[i]],Sequence@@lismin[[i+1;;]]},{i,1,Length[lis]}];
Flatten[Table[expr,Evaluate[Sequence@@#]]&/@listab,nlis]];


convExp[data_,n_:All]:=Module[{dat},dat={#[[1]],Log[#[[2]]]}&/@take[data,n];LinearModelFit[dat,N,N]];


Options[convExpPlot]={optData->{},optFitted->{}};
convExpPlot[data_,n_:All,opt:OptionsPattern[]]/;(Head[n]=!=Rule):=Module[{dat,convexp},
dat=take[data,n];
convexp=convExp[data,n];
Print[convexp];
Show[ListLogPlot[dat,OptionValue[optData]],LogPlot[Exp@convexp[x],{x,dat[[1,1]],dat[[-1,1]]},Evaluate@OptionValue[optFitted]],Frame->True]];


convPow[data_,n_:All]:=Module[{dat},dat={#[[1]],Log[#[[2]]]}&/@take[data,n];LinearModelFit[dat,Log[N],N]];


Options[convPowPlot]={optData->{},optFitted->{}};
convPowPlot[data_,n_:All,opt:OptionsPattern[]]/;(Head[n]=!=Rule):=Module[{dat,convpow},
dat=take[data,n];
convpow=convPow[data,n];
Print[convpow];
Show[ListLogLogPlot[dat,OptionValue[optData]],LogLogPlot[Exp@convpow[x],{x,dat[[1,1]],dat[[-1,1]]},Evaluate@OptionValue[optFitted]],Frame->True]];


count[expr_,x_]:=Plus@@(Count[expr,#,{0,Infinity},Heads->True]&/@Flatten[{x}]);


dChange[expr_,y_,x_,u_,t_,trans_]:=DSolveChangeVariables[Inactive[DSolve][expr,y,x],u,t,trans][[1]];
dChange[expr_,y_,x_,t_,trans_]:=DSolveChangeVariables[Inactive[DSolve][expr,y,x],y,t,trans][[1]];


deleteFactor[expr_Times,mem_]:=DeleteCases[expr,temp_/;FreeQ[temp,Alternatives@@mem,Heads->True],1];
deleteFactor[expr_,mem_]:=expr;
deleteFactor[expr_List,mem_]:=deleteFactor[#,mem]&/@expr;


derivL[f_[x_?AtomQ]]:={f\[Diamond]x,f\[Diamond]x\[Diamond]x};
derivL[f_[x_?AtomQ,y_?AtomQ]]:={f\[Diamond]x,f\[Diamond]y,f\[Diamond]x\[Diamond]y,f\[Diamond]x\[Diamond]x,f\[Diamond]y\[Diamond]y};
derivL[flist_List]:=derivL[#//Flatten]&/@flist//Flatten;


derivR[f_[x_?AtomQ]]:={"d"\[Diamond]x\[Diamond]"."\[Diamond]f,"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f};
derivR[f_[x_?AtomQ,y_?AtomQ]]:={"d"\[Diamond]x\[Diamond]"."\[Diamond]f,"d"\[Diamond]y\[Diamond]"."\[Diamond]f,"d"\[Diamond]x\[Diamond]y\[Diamond]"."\[Diamond]f,"d"\[Diamond]x\[Diamond]x\[Diamond]"."\[Diamond]f,"d"\[Diamond]y\[Diamond]y\[Diamond]"."\[Diamond]f};
derivR[flist_List]:=derivR[#//Flatten]&/@flist//Flatten;


dFunc[f_[x_?AtomQ]]:={f[x],f'[x],f''[x]};
dFunc[\!\(\*SuperscriptBox[\(f_\), 
TagBox[
RowBox[{"(", "a_", ")"}],
Derivative],
MultilineFunction->None]\)[x_?AtomQ]]:=Table[\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", "n", ")"}],
Derivative],
MultilineFunction->None]\)[x],{n,a,0,-1}];
dFunc[f_[x_?AtomQ,y_?AtomQ]]:={f[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]};
dFunc[f_[x_?AtomQ,y_?AtomQ,z_?AtomQ]]:={f[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]};
dFunc[fcn_List]:=dFunc[#]&/@fcn//Flatten;


diag[vec_?VectorQ]:=DiagonalMatrix[vec];
diag[mat_?MatrixQ]:=Module[{i},Table[mat[[i,i]],{i,Length[mat]}]];


SetAttributes[divide,Listable];
divide[a_,b_]:=If[b===0||b===0.,HoldForm[a/b],a/b];


dRule[f_[x_]->expr_]:={f[x]->expr,f'[x]->D[expr,x],f''[x]->D[expr,x,x]};
dRule[f_[x_,y_]->expr_]:={f[x,y]->expr,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,x],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,x,x],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->D[expr,y,y]};
dRule[flist_List]:=dRule[#]&/@flist//Flatten;


drop[m_,parts__List]/;Length@{parts}<=ArrayDepth[m]:=m[[##]]&@@MapThread[Complement,{Range@Dimensions[m,Length@{parts}],{parts}}];


Options[eqEigen]={timesQ->False};
eqEigen[{flist_List,reflist___List},{eqlist_List,matname_String},\[Lambda]_,s_String:"",opt:OptionsPattern[]]:=Module[{eqlistp,dim,x,y,sx,sy,mattemp,mat0,mat1,m,a},
If[OptionValue[timesQ]==False,times=Times;];
If[prelinearize=!={{flist,reflist},s},preLinearize[{flist,reflist},s];];
If[ValueQ[maxPow]==False,maxPow=Cases[eqlist,\[Lambda]^(pow_:1):>pow,Infinity]//Max];
eqlistp=(PadRight[#,maxPow+1]&/@CoefficientList[eqlist,\[Lambda]])//Transpose;
dim=Length[List@@flist[[1]]];
Which[dim==1,
x=Identity@@flist[[1]];
sx=ToString[x];
mattemp=Table[times[D[eqlistp[[p,i]],D[flist[[j]],x,x]],ToExpression["d"<>sx<>sx]]+times[D[eqlistp[[p,i]],D[flist[[j]],x]],ToExpression["d"<>sx]]+times[D[eqlistp[[p,i]],flist[[j]]],ToExpression["id"<>s]]+ToExpression["zero"<>s],{p,maxPow+1},{i,nEq\[Vee]s},{j,nEq\[Vee]s}]//.replrule\[Vee]s;,
dim==2,
{x,y}=List@@flist[[1]];
{sx,sy}=ToString/@{x,y};
mattemp=Table[times[D[eqlistp[[i]],D[flist[[j]],x,x]],ToExpression["d"<>sx<>sx]]+times[D[eqlistp[[i]],D[flist[[j]],y,y]],ToExpression["d"<>sy<>sy]]+times[D[eqlistp[[i]],D[flist[[j]],x,y]],ToExpression["d"<>sx<>sy]]+times[D[eqlistp[[i]],D[flist[[j]],x]],ToExpression["d"<>sx]]+times[D[eqlistp[[i]],D[flist[[j]],y]],ToExpression["d"<>sy]]+times[D[eqlistp[[i]],flist[[j]]],ToExpression["id"<>s]]+ToExpression["zero"<>s],{p,maxPow+1},{i,nEq\[Vee]s},{j,nEq\[Vee]s}]//.replrule\[Vee]s;];
mat0=ConstantArray[zero\[Vee]s,{nEq\[Vee]s,nEq\[Vee]s}];
mat1=Table[If[i==j,id\[Vee]s,zero\[Vee]s],{i,nEq\[Vee]s},{j,nEq\[Vee]s}];
If[maxPow==1,m=mattemp[[1]];a=-mattemp[[2]];,
m=Table[If[i==0,mattemp[[j+1]],If[i==j,mat1,mat0]],{i,0,maxPow-1},{j,0,maxPow-1}]//ArrayFlatten;
a=Table[If[i==0&&j==maxPow-1,-mattemp[[maxPow+1]],If[i==j+1,mat1,mat0]],{i,0,maxPow-1},{j,0,maxPow-1}]//ArrayFlatten;];
matname\[Diamond]s\[DotEqual]{m,a};];
eqEigen[{flist_List,reflist___List},{y__List},\[Lambda]_,s_String:"",opt:OptionsPattern[]]:=eqEigen[{flist,reflist},#,\[Lambda],s,opt]&/@{y};


Options[eqLinearize]={timesQ->False};
eqLinearize[{flist_List,reflist___List},{eqlist_List,eqname_String,matname_String,fileQ_:False,eqlistmat_String:""},s_String:"",opt:OptionsPattern[]]:=Module[{dim,x,y,sx,sy,eqtemp,mattemp},
If[OptionValue[timesQ]==False,times=Times;];
If[prelinearize=!={{flist,reflist},s},preLinearize[{flist,reflist},s];];
eqtemp=eqlist//.replrule\[Vee]s;
If[eqtemp===eqlist,Print["Already replaced; Return"]; Return[];];
dim=Length[List@@flist[[1]]];
Which[dim==1,
x=Identity@@flist[[1]];
sx=ToString[x];
mattemp=Table[times[D[eqlist[[i]],D[flist[[j]],x,x]],ToExpression["d"<>sx<>sx]]+times[D[eqlist[[i]],D[flist[[j]],x]],ToExpression["d"<>sx]]+times[D[eqlist[[i]],flist[[j]]],ToExpression["id"<>s]]+ToExpression["zero"<>s],{i,Length[eqlist]},{j,Length[flist]}]//.replrule\[Vee]s;,
dim==2,
{x,y}=List@@flist[[1]];
{sx,sy}=ToString/@{x,y};
mattemp=Table[times[D[eqlist[[i]],D[flist[[j]],x,x]],ToExpression["d"<>sx<>sx]]+times[D[eqlist[[i]],D[flist[[j]],y,y]],ToExpression["d"<>sy<>sy]]+times[D[eqlist[[i]],D[flist[[j]],x,y]],ToExpression["d"<>sx<>sy]]+times[D[eqlist[[i]],D[flist[[j]],x]],ToExpression["d"<>sx]]+times[D[eqlist[[i]],D[flist[[j]],y]],ToExpression["d"<>sy]]+times[D[eqlist[[i]],flist[[j]]],ToExpression["id"<>s]]+ToExpression["zero"<>s],{i,Length[eqlist]},{j,Length[flist]}]//.replrule\[Vee]s;];
{eqname\[Diamond]"="\[Diamond]eqtemp,matname\[Diamond]"="\[Diamond]mattemp}//ReleaseHold;
If[fileQ==True,Put[eqtemp,eqname]; Put[mattemp,matname];];
If[eqlistmat!="",Put[optimize[{eqtemp,mattemp}],eqlistmat];];];
eqLinearize[{flist_List,reflist___List},{y__List},s_String:"",opt:OptionsPattern[]]:=eqLinearize[{flist,reflist},#,s,opt]&/@{y};


SetAttributes[eqProcess,HoldRest];
Options[eqProcess]={timesQ->False};
eqProcess[func_,get[file___],bdyprerepl_List,s_String:"",opt:OptionsPattern[]]:=(get[file];
bdyCondition[toList[func,2],bdyprerepl,s,opt];)
eqProcess[func_,eq_,bdyprerepl_List,s_String:"",opt:OptionsPattern[]]:=(eqLinearize[toList[func,2],{toList[eq],"eqlist"<>s,"mat"<>s},s,opt];
bdyCondition[toList[func,2],bdyprerepl,s,opt];)
eqProcess[func_,put[eq_],s_String:"",opt:OptionsPattern[]]:=eqLinearize[toList[func,2],{toList[eq],"eqlist"<>s,"mat"<>s,True,"eqlistmat"<>s},s,opt];
eqProcess[func_,eq_,s_String:"",opt:OptionsPattern[]]:=eqLinearize[toList[func,2],{toList[eq],"eqlist"<>s,"mat"<>s},s,opt];

eqProcess[func_,eq_,bdyprerepl_List,\[Lambda]_?AtomQ,s_String:"",opt:OptionsPattern[]]:=(eqEigen[toList[func,2],{toList[eq],"mat"<>s},\[Lambda],s,opt];
bdyCondition[toList[func,2],bdyprerepl,\[Lambda],s,opt];)
eqProcess[func_,eq_,\[Lambda]_?AtomQ,s_String:"",opt:OptionsPattern[]]:=eqEigen[toList[func,2],{toList[eq],"mat"<>s},\[Lambda],s,opt];


findPeaks[list_List]:=list[[FindPeaks[list[[;;,2]]][[;;,1]]]];


findPeaksPlot[list_List,ps:(_?NumericQ):0.02,opt:OptionsPattern[]]:=ListLinePlot[list,Epilog->{Red,PointSize[ps],Point[findPeaks[list]]},opt];


findRoot[eq_,x_,plists__List,opt:OptionsPattern[]]:=Module[{subs},
subs=MapThread[Rule,{plists}[[;;,1;;2]]\[Transpose]];
FindRoot[eq/.subs,x,opt];
Table[FindRoot[eq,x,opt],plists]];


frameLabel[lx_,ly_]:={Frame->True,FrameLabel->{style[lx],Rotate[style[ly],-Pi/2]}};
frameLabel[lx_,ly_,lt_]:={Frame->True,FrameLabel->{style[lx],Rotate[style[ly],-Pi/2],style[lt]}};
frameLabel[framelabel__]:={Frame->True,RotateLabel->False,FrameLabel->{framelabel}};


funcVar[func_,n_:All][expr_]:=Flatten[Cases[expr,Verbatim[func][x__]:>{x},{0,\[Infinity]}]][[n]];
funcVar[func_,n_:All][expr_List]:=funcVar[func,n][#]&/@expr;


SetAttributes[get,HoldAll];
get[name__,rule___Rule]:=Module[{nam},
nam=List@@(Unevaluated/@Hold[name]);
set[nam,release["<<"\[Diamond]{name}]/.{rule}]];


getFunc[expr_]:=Union@Cases[expr,\!\(\*SuperscriptBox[\(f_Symbol\), 
TagBox[
RowBox[{"(", "n__", ")"}],
Derivative],
MultilineFunction->None]\)[z__Symbol]:>f[z],{0,Infinity}];


getVar[expr_]:=Union@Cases[expr,\!\(\*SuperscriptBox[\(f_Symbol\), 
TagBox[
RowBox[{"(", "n__", ")"}],
Derivative],
MultilineFunction->None]\)[z__Symbol]:>{z},{0,Infinity}];


hold=HoldForm;


imaginary[{expr__List}]:=imaginary/@{expr};
imaginary[expr_]:=Select[expr,(Im[#]!=0)&];


SetAttributes[index,HoldFirst];
index[Or[reg__]]:=Module[{regh=Hold[reg]},Union[index[#]&/@regh//release]];
index[And[reg__]]:=Module[{regh=Hold[reg]},Intersection[index[#]&/@regh//release]];
index[{reg__}]:=index[Or[reg]];
index[head_[x_,a_?NumericQ]]:=Position[x,x0_/;head[x0,a]]//Flatten;
index[head_[a_?NumericQ,x_,b_?NumericQ]]:=Position[x,x0_/;head[a,x0,b]]//Flatten;
index[expr_,{n_Integer},s_String:""]:=Flatten[index[expr]+(n-1) dimGrid\[Vee]s];
index[expr_,{n__Integer},s_String:""]:=Flatten[index[expr,{#},s]&/@{n}];
index[expr_,nEq_Integer,s_String:""]:=Table[index[expr]+(n-1) dimGrid\[Vee]s,{n,nEq}]//Flatten;


insert[list_,val_,pos_]:=Join[val,list][[Ordering@Join[pos,Range@Length@list]]];


interp[x_][y1_,y2_]:=(1-x)/2 y1+(1+x)/2 y2;


interp[x_,y_,s_String:"",opt:OptionsPattern[]]:=Interpolation[{x,y}\[Transpose],opt];
interp[x_,y_,z_,s_String:"",opt:OptionsPattern[]]:=Module[{px,py,pz,xx,yy,zz,one},
If[(NumericQ[xPeriod\[Vee]s]||NumericQ[yPeriod\[Vee]s])=!=True,Interpolation[{{x,y}\[Transpose],z}\[Transpose],opt],
{px,py,pz}=Partition[#,nyGrid\[Vee]s+1]&/@{x,y,z};
If[NumericQ[xPeriod\[Vee]s],
one=Table[1,{nyGrid\[Vee]s+1}];
xx=Append[px,N[xPeriod\[Vee]s one,prec]]//Flatten;
yy=Append[py,py[[1]]]//Flatten;
zz=Append[pz,pz[[1]]]//Flatten;];
If[NumericQ[yPeriod\[Vee]s],
one=Table[1,{nxGrid\[Vee]s+1}];
xx=Append[px\[Transpose],px\[Transpose][[1]]]\[Transpose]//Flatten;
yy=Append[py\[Transpose],N[yPeriod\[Vee]s one,prec]]\[Transpose]//Flatten;
zz=Append[pz\[Transpose],pz\[Transpose][[1]]]\[Transpose]//Flatten;];
Interpolation[{{xx,yy}\[Transpose],zz}\[Transpose],opt]]];


Options[interpF]={derivQ->False};
interpF[f_[x_?AtomQ],s_String:"",suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]x\[Diamond]x}//ReleaseHold;
rt={f,f\[Diamond]x,f\[Diamond]x\[Diamond]x}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=interp[x,#2,s]]&,{lft,rt}],MapThread[hold[#1=interp[x,#2,s]]&,{{lft[[1]]},{rt[[1]]}}]]];
interpF[f_[x_?AtomQ,y_?AtomQ],s_String:"",suf_String:"f",opt:OptionsPattern[]]:=Module[{lft,rt},
lft={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]x,f\[Diamond]suf\[Diamond]y\[Diamond]y}//ReleaseHold;
rt={f,f\[Diamond]x,f\[Diamond]y,f\[Diamond]x\[Diamond]y,f\[Diamond]x\[Diamond]x,f\[Diamond]y\[Diamond]y}//ReleaseHold;
If[OptionValue[derivQ]==True,MapThread[hold[#1=interp[x,y,#2,s]]&,{lft,rt}],MapThread[hold[#1=interp[x,y,#2,s]]&,{{lft[[1]]},{rt[[1]]}}]]];
interpF[flist_List,s_String:"",suf_String:"f",opt:OptionsPattern[]]:=interpF[#//Flatten,s,suf,opt]&/@flist//Flatten;


linearMap[{x1_,x2_}->{y1_,y2_}]:=((#-x1) (y2-y1)/(x2-x1)+y1)&;
linearMap[{y1_,y2_}]:=linearMap[{-1,1}->{y1,y2}];
linearMap[x_,{x1_,x2_}->{y1_,y2_}]:=linearMap[{x1,x2}->{y1,y2}][x];
linearMap[x_,{y1_,y2_}]:=linearMap[{y1,y2}][x];


SetAttributes[listData,HoldAll];
listData[fun_,plists__List]:=Flatten[If[$parallelQ===True,ParallelTable,Table][{Sequence@@{plists}[[;;,1]],fun},plists],Length[{plists}]-1];


SetAttributes[listDensityPlot,HoldAll];
listDensityPlot[fun_,plists__List,opt:OptionsPattern[]]:=ListDensityPlot[listData[fun,plists],opt];


listFormat[m_List,n__]:=Map[Table[1,Evaluate[Sequence@@Partition[Dimensions[m[[n]]],1]]]#&,m,{Length[{n}]}];


listPart[x_List,spec__]:=x[[spec]];


SetAttributes[listLinePlot,HoldAll];
listLinePlot[fun_,plist_List,opt:OptionsPattern[]]:=ListLinePlot[listData[fun,plist],opt]; 


SetAttributes[listPlot,HoldAll];
listPlot[fun_,plist_List,opt:OptionsPattern[]]:=ListPlot[listData[fun,plist],opt];


SetAttributes[listPlot3D,HoldAll];
listPlot3D[fun_,plists__List,opt:OptionsPattern[]]:=ListPlot3D[listData[fun,plists],opt];


SetAttributes[listSurfacePlot3D,HoldAll];
listSurfacePlot3D[fun_,plists__List,opt:OptionsPattern[]]:=ListSurfacePlot3D[listData[fun,plists],opt];


listSeries[expr_List,{x_,x0_,ord_List}]:=Module[{diff,i,order},
diff=Length[expr]-Length[ord];
Which[diff<0,Abort[],
diff==0,order=ord,
diff>0,order=Flatten@Join[ord,Table[ord[[-1]],{i,diff}]]];
MapThread[Series[#1,{x,x0,#2}]&,{expr,order}]];


listSeriesCoeff[expr_List,{x_,x0_,ord_List}]:=Module[{diff,i,order},
diff=Length[expr]-Length[ord];
Which[diff<0,Abort[],
diff==0,order=ord,
diff>0,order=Flatten@Join[ord,Table[ord[[-1]],{i,diff}]]];
MapThread[SeriesCoefficient[#1,{x,x0,#2}]&,{expr,order}]];


map[heads_List,vars_]:=Map[#[Sequence@@(Flatten[{vars}])]&,heads];


memory:={memoryForm[MemoryInUse[]]<>" in use",memoryForm[MemoryAvailable[]]<>" available"};


memoryForm[mem_,n_:3]:=Which[10^3<=mem<10^6,ToString@NumberForm[N[10^-3 mem],n]<>"\[ThinSpace]K",10^6<=mem<10^9,ToString@NumberForm[N[10^-6 mem],n]<>"\[ThinSpace]M",10^9<=mem<10^12,ToString@NumberForm[N[10^-9 mem],n]<>"\[ThinSpace]G",True,ToString[mem]];


nD[x_List,y_List]:=Differences[y]/Differences[x];


SetAttributes[noInfinity,HoldAll];
noInfinity[expr_]:=Quiet[expr]/.{Indeterminate->Nothing,ComplexInfinity->Nothing};


SetAttributes[noSimplify,HoldFirst];
noSimplify[expr_,lev_:1]:=Block[{Simplify,FullSimplify},Simplify=Identity; If[lev==2,FullSimplify=Identity;]; expr];


nPower[x_List,y_List]:=(x[[1;;-2]]+x[[2;;-1]])/(y[[1;;-2]]+y[[2;;-1]]) nD[x,y];


numerator[expr_]:=Numerator@Factor[expr];
numerator[expr_,mem_,lev_:1]:=deleteFactor[Which[lev==0,Identity,lev==1,Simplify,lev==2,FullSimplify]@Numerator@Factor[expr],mem];


numeric[{expr__List}]:=numeric/@{expr};
numeric[expr_]:=Select[expr,NumericQ];


optimize[expr_]:=Experimental`OptimizeExpression[expr];


periodicAppend[mat_]:=Module[{mattr},mattr=Append[mat,mat[[1]]]\[Transpose];Append[mattr,mattr[[1]]]\[Transpose]];


perturb[f_,dim_Integer:1,s0_String:"0",s1_String:"\[Delta]",ep_:\[Epsilon]]:=Which[dim==1,f->(Evaluate[(f\[Diamond]s0)[#]+ep (s1\[Diamond]f)[#]]&),
dim==2,f->(Evaluate[(f\[Diamond]s0)[#1,#2]+ep (s1\[Diamond]f)[#1,#2]]&),
dim==3,f->(Evaluate[(f\[Diamond]s0)[#1,#2,#3]+ep (s1\[Diamond]f)[#1,#2,#3]]&)]//ReleaseHold;
SetAttributes[perturb,Listable];


perturbed[expr_,hlist_List,s_String:"\[Delta]"]:=expr/.MapThread[Rule,{hlist,s\[Diamond]Evaluate[hlist]//release}];


positive[{expr__List}]:=positive/@{expr};
positive[expr_List]:=Select[expr,Positive];


preLinearize[{flist_List,reflist___List},s_String:""]:=(prelinearize={{flist,reflist},s};
nEq\[Diamond]s\[DotEqual]Length[flist];
replrule\[Diamond]s\[DotEqual](replRule[{flist,reflist}]);
calcfderiv\[Diamond]s\[DotEqual](calcDeriv[flist]//unmap);
calcrefderiv\[Diamond]s\[DotEqual](calcDeriv[reflist]//unmap);
calcfrefderiv\[Diamond]s\[DotEqual](calcDeriv[{flist,reflist}]//unmap);
finterpf\[Diamond]s\[DotEqual](interpF[flist,s]//unmap);
refinterpf\[Diamond]s\[DotEqual](interpF[reflist,s]//unmap);
calcfinterp\[Diamond]s\[DotEqual](calcInterp[flist]//unmap);
calcrefinterp\[Diamond]s\[DotEqual](calcInterp[reflist]//unmap);
vars\[Diamond]s\[DotEqual]Flatten[{List@@flist[[1]],{flist,reflist}/.replrule\[Vee]s,release@derivL[{flist,reflist}]}];
solsave\[Diamond]s\[DotEqual]Flatten[{flist/.replrule\[Vee]s,lastGrid\[Vee]s}];
hlist\[Diamond]s\[DotEqual]Unevaluated/@Head/@flist;
hlistf\[Diamond]s\[DotEqual]Unevaluated@@@(Evaluate[Head/@flist]\[Diamond]f);
{{nEq\[Diamond]s,replrule\[Diamond]s,calcfderiv\[Diamond]s,calcrefderiv\[Diamond]s,calcfrefderiv\[Diamond]s,finterpf\[Diamond]s,refinterpf\[Diamond]s,calcfinterp\[Diamond]s,calcrefinterp\[Diamond]s,vars\[Diamond]s,solsave\[Diamond]s,hlist\[Diamond]s,hlistf\[Diamond]s},{calcfref\[Diamond]s,calcbdyind\[Diamond]s,calcrefred\[Diamond]s}});


range[{x_,x0_}]:={x,toList[x0]};
range[{x_,xmin_?AtomQ,xmax_?AtomQ}]:={x,Range[xmin,xmax]};
range[{x_,xmin_?AtomQ,xmax_?AtomQ,dx_?AtomQ}]:={x,Range[xmin,xmax,dx]};
range[{x_,xi_List,dxi_List}]:={x,Range@@@MapThread[Append,{Partition[xi,2,1],dxi}]//Flatten//DeleteAdjacentDuplicates};
range[xi_List,dxi_List]:=Range@@@MapThread[Append,{Partition[xi,2,1],dxi}]//Flatten//DeleteAdjacentDuplicates;


reflect[plot_,v_,opt:OptionsPattern[]]:=Show[MapAt[GeometricTransformation[#1,ReflectionTransform[v]]&,plot,{1}],PlotRange->All,opt];
reflectX[plot_,opt:OptionsPattern[]]:=Show[plot,reflect[plot,{0,-1}],PlotRange->All,opt];
reflectY[plot_,opt:OptionsPattern[]]:=Show[plot,reflect[plot,{-1,0}],PlotRange->All,opt];
reflectXY[plot_,opt:OptionsPattern[]]:=reflectY[reflectX[plot],opt];


release=ReleaseHold;


release2=ReleaseHold@ReleaseHold[#]&;


releaseAll=Map[ReleaseHold,#,Infinity]&;


removeAll:=Remove[Evaluate[$Context<>"*"]];
removeAll::usage="removeAll removes all symbols in the current context";


replRule[]:={};
replRule[f_[x_?AtomQ]]:={f[x]->f,f'[x]->f\[Diamond]x,f''[x]->f\[Diamond]x\[Diamond]x}//ReleaseHold;
replRule[f_[x_?AtomQ,y_?AtomQ]]:={f[x,y]->f,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]x\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]x\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]->f\[Diamond]y\[Diamond]y}//ReleaseHold;
replRule[f_[x_?AtomQ,y_?AtomQ,z_?AtomQ]]:={f[x,y,z]->f,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]z,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x\[Diamond]z,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]y\[Diamond]z,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]x\[Diamond]x,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]y\[Diamond]y,\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y,z]->f\[Diamond]z\[Diamond]z}//ReleaseHold;
replRule[flist_List]:=replRule[#//Flatten]&/@flist//Flatten;


replInterp[f_[x_?AtomQ],suf_String:"f"]:=Module[{lft,rt},
lft={f[x],f'[x],f''[x]};
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]x\[Diamond]x}//ReleaseHold;
MapThread[Rule,{lft,map[rt,x]}]];
replInterp[f_[x_?AtomQ,y_?AtomQ],suf_String:"f"]:=Module[{lft,rt},
lft={f[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y],\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[x,y]};
rt={f\[Diamond]suf,f\[Diamond]suf\[Diamond]x,f\[Diamond]suf\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]y,f\[Diamond]suf\[Diamond]x\[Diamond]x,f\[Diamond]suf\[Diamond]y\[Diamond]y}//ReleaseHold;
MapThread[Rule,{lft,map[rt,{x,y}]}]];
replInterp[flist_List,suf_String:"f"]:=replInterp[#//Flatten,suf]&/@flist//Flatten;


restart[]:=(clearAll; Get["init.m"]; <<spNDSolve.m; setdir;);


round[x_]:=If[FractionalPart[x]==0,IntegerPart[x],x];
SetAttributes[round,Listable];


rule[lhs_,rhs_]:=Thread@Rule[lhs,rhs];


ruleToSet:=(HoldForm[##]/.Rule->Set)&;


series0[expr_,ep_:\[Epsilon]]:=SeriesCoefficient[expr,{ep,0,0}];


series1[expr_,ep_:\[Epsilon]]:=SeriesCoefficient[expr,{ep,0,1}];


seriesExpand[f_[x_?AtomQ],{x_,x0_,pmin_,num_,dp_:1},s_String:""]:={f->Function[x,Sum[Subscript[(f\[Diamond]s), i] (x-x0)^i//release,{i,pmin,pmin+(num-1)dp,dp}]//Evaluate],
coeffToDiff[Table[Subscript[(f\[Diamond]s), i]//release,{i,pmin,pmin+(num-1)dp,dp}],x,s]};
seriesExpand[f_[y__?AtomQ],{x_,x0_,pmin_,num_,dp_:1},s_String:""]:={f->Function[{y},Sum[Subscript[(f\[Diamond]s), i][Sequence@@DeleteCases[{y},x]](x-x0)^i//release,{i,pmin,pmin+(num-1)dp,dp}]//Evaluate],
coeffToDiff[Table[Subscript[(f\[Diamond]s), i][Sequence@@DeleteCases[{y},x]]//release,{i,pmin,pmin+(num-1)dp,dp}],x,Position[{y},x][[1,1]],s]};
seriesExpand[func_List,{x_,x0_,pmin_,num_,dp_:1},s_String:""]:=Flatten/@(seriesExpand[#,{x,x0,pmin,num,dp},s]&/@func//Transpose);
seriesExpand[func_List,{x_,x0_,pmin_List,num_,dp_:1},s_String:""]:=Module[{diff,i,ptemp},
diff=Length[func]-Length[pmin];
Which[diff<0,Abort[],
diff==0,ptemp=pmin,
diff>0,ptemp=Flatten@Join[pmin,Table[pmin[[-1]],{i,diff}]]];
Flatten/@(MapThread[seriesExpand[#1,{x,x0,#2,num,dp},s]&,{func,ptemp}]//Transpose)];

seriesExpand[f_[x_?AtomQ],{x_,x0_,pmin_,num_,dp_:1},s_String:"c",{ppmin_,nnum_,dpp_:1},ss_String:"cc"]:=(f->Function[x,Sum[Subscript[(f\[Diamond]s), i] (x-x0)^i//release,{i,pmin,pmin+(num-1)dp,dp}]+Log[x]Sum[Subscript[(f\[Diamond]ss), i] (x-x0)^i//release,{i,ppmin,ppmin+(nnum-1)dpp,dpp}]//Evaluate]);
seriesExpand[f_[y__?AtomQ],{x_,x0_,pmin_,num_,dp_:1},s_String:"c",{ppmin_,nnum_,dpp_:1},ss_String:"cc"]:=
(f->Function[{y},Sum[Subscript[(f\[Diamond]s), i][Sequence@@DeleteCases[{y},x]](x-x0)^i//release,{i,pmin,pmin+(num-1)dp,dp}]+Log[x]Sum[Subscript[(f\[Diamond]ss), i][Sequence@@DeleteCases[{y},x]](x-x0)^i//release,{i,ppmin,ppmin+(nnum-1)dpp,dpp}]//Evaluate]);
seriesExpand[func_List,{x_,x0_,pmin_,num_,dp_:1},s_String:"c",{ppmin_,nnum_,dpp_:1},ss_String:"cc"]:=seriesExpand[#,{x,x0,pmin,num,dp},s,{ppmin,nnum,dpp},ss]&/@func;


set[a_List,b_List]:=MapThread[Set,{a,b}];
set[a_HoldForm,b_HoldForm]:=Table[Identity@@MapThread[Set,{{a[[i]]},{b[[i]]}}],{i,Length[a]}];


setdir:=SetDirectory[NotebookDirectory[]];


simplify=FullSimplify;
zSimplify[expr_]:=Module[{r},Simplify[Simplify[expr/.z->Sqrt[1-r^2],r>0]/.r->Sqrt[1-z^2],z>0]];


solve[expr_, vars_] := Module[{vars0=Flatten@{vars},vars1},
vars1=Unique[]/@ vars0;
Solve[SubStar[(expr/.rule[vars0,vars1])],vars1]/.rule[vars1,vars0]];


solution=(#/.(y_->f_):>Inactive[Set][y\[Diamond]"sol",y\[Diamond]"sol"\[DotEqual]f])&;


SetAttributes[spNDEigen,HoldAll];
Options[spNDEigen]={calcrefredQ->False,eigenVecQ->False,minPrec->0,noInfinityQ->Fals,"D"->False};
spNDEigen[x_,fx_,nxGrid0_,s_String:"",opt:OptionsPattern[]]:=Block[{interpQ=False},
If[nxGrid0!=lastGrid\[Vee]s,interpQ=True;];
lastGrid\[Diamond]s\[DotEqual]nxGrid0;
cheb[x,fx,nxGrid0,s,FilterRules[{opt},Options[cheb]]];
calcbdyind\[Vee]s//release;

If[OptionValue[calcrefredQ]==False,calcrefderiv\[Vee]s//release;,calcrefred\[Vee]s//release;];
lhs\[Diamond]s\[DotEqual]ArrayFlatten/@(mat\[Vee]s);

bdyReplace[bdyrepl\[Vee]s//release,s];
eig=If[OptionValue[eigenVecQ]==False,Eigenvalues,Eigensystem][lhs\[Vee]s];
If[ValueQ[output]==False,eig,output]];
spNDEigen[x_,fx_,nxGrid0_,s_String:"",plists__List,opt:OptionsPattern[]]:=Block[{n=1,out},
outputs=continue[out=spNDEigen[x,fx,nxGrid0,s,opt],plists]];


SetAttributes[spNDSolve,HoldAll];
Options[spNDSolve]={calcrefredQ->False,epValue->10^-9,eqlistmatQ->False,iniQ->True,linearQ->False,lsqrQ->False,maxChange->10^9,minPrec->0,"D"->False};
spNDSolve[x_,fx_,nxGrid0_,s_String:"",opt:OptionsPattern[]]:=Block[{interpQ=False,ep=OptionValue[epValue],mchange=OptionValue[maxChange],change=1,df,nprint=1},
If[{fx,nxGrid0}!=lastGrid\[Vee]s,interpQ=True;];
If[interpQ===True,finterpf\[Vee]s//release;];
lastGrid\[Diamond]s\[DotEqual]{fx,nxGrid0};
cheb[x,fx,nxGrid0,s,FilterRules[{opt},Options[cheb]]];
calcbdyind\[Vee]s//release;

If[OptionValue[linearQ]==True,set[hlist\[Vee]s,Table[0one,nEq]]];
Which[OptionValue[iniQ]===True,calcfref\[Vee]s;,
interpQ===True,calcfinterp\[Vee]s//release; calcref\[Vee]s;];
If[OptionValue[calcrefredQ]==False,calcrefderiv\[Vee]s//release;];

While[change>ep,
If[OptionValue[calcrefredQ]==True,calcrefred\[Vee]s//release;];
calcfderiv\[Vee]s//release;
If[OptionValue[eqlistmatQ]==True,{eqlist\[Diamond]s,mat\[Diamond]s}\[DotEqual]eqlistmat\[Vee]s[[1]];];
lhs\[Diamond]s\[DotEqual]ArrayFlatten[mat\[Vee]s];
rhs\[Diamond]s\[DotEqual]-Flatten[eqlist\[Vee]s];
bdyReplace[bdyrepl\[Vee]s//release,s];
df=If[OptionValue[lsqrQ]==False,LinearSolve,LeastSquares][lhs\[Vee]s,rhs\[Vee]s];
If[OptionValue[linearQ]==True,
set[hlist\[Vee]s,Partition[df,dimGrid\[Vee]s]];Break[];];
change=Norm[df];

If[nprint==1,changes={change};nprint++;,AppendTo[changes,change];];
If[change>mchange,Print["change > ",ScientificForm@N[mchange]];Abort[];];

addTo[hlist\[Vee]s,Partition[df,dimGrid\[Vee]s]];];
output];
spNDSolve[x_,fx_,nxGrid0_,s_String:"",plists__List,opt:OptionsPattern[]]:=Block[{n=1},
outputs=continue[spNDSolve[x,fx,nxGrid0,s,iniQ:>If[n==1,(n++; OptionValue[iniQ]),False],opt],plists]];


SetAttributes[spNIntegrate,HoldAll];
Options[spNIntegrate]={minPrec->0};
spNIntegrate[x_,fx_,nxGrid0_,expr_,s_String:"",opt:OptionsPattern[]]:=(cheb[x,fx,nxGrid0,s,FilterRules[{opt},Options[cheb]]];
lhs\[Diamond]s\[Diamond]"="\[Diamond]"d"\[Diamond]x//release;
rhs\[Diamond]s\[DotEqual]expr;
lhs\[Diamond]s[[1]]\[DotEqual]id\[Vee]s[[1]];
rhs\[Diamond]s[[1]]\[DotEqual]0;
LinearSolve[lhs\[Vee]s,rhs\[Vee]s]);


take[list_,n_]:=If[(Length[list]>=n)===True,Take[list,n],list];


SetAttributes[timing,HoldAll];
timing[expr_]:=AbsoluteTiming[expr];
timing[expr__]:=(List@@AbsoluteTiming/@Hold[expr])[[All,1]];


toHeldExpression=ToExpression[#,StandardForm,HoldForm]&;


toList[x_/;Head[x]=!=List]:={x};
toList[x_]:=x;
toList[x_/;Head[x]=!=List,2]:={{x}};
toList[x_?VectorQ,2]:={x};
toList[x_,2]:=x;


SetAttributes[toString,{HoldAll,Listable}];
toString[x_]:=ToString[Unevaluated[x]];


translate[plot_,v_,opt:OptionsPattern[]]:=Show[MapAt[GeometricTransformation[#1,TranslationTransform[v]]&,plot,{1}],PlotRange->All,opt];


SetAttributes[unevaluate,{HoldAll,Listable}];
unevaluate[expr_]:=Identity@@Identity@@MapAll[Unevaluated,Hold[expr],Heads->True];


union=DeleteCases[Union[#],0]&;


unmap[list_,head_:HoldForm]:=head@@Replace[Hold[Evaluate[list]],head[x__]:>x,Infinity];


(*The following must be used with diffgeo.m*)


deTurck:=(\[Xi]=contract[lower[Christoffel-\[CapitalGamma]bar,{1}],{2,3}];
del\[Xi]=Symmetrize@Table[D[\[Xi],coord[[ii]]],{ii,1,dimen}]-Sum[Christoffel[[ii]]\[Xi][[ii]],{ii,1,dimen}];  (*del\[Xi]=symmetrize@covariant[\[Xi]]*)
\[Xi]2=contract[\[Xi]**\[Xi]]//noSimplify;)
