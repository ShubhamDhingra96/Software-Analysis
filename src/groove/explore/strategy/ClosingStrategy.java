/*
 * GROOVE: GRaphs for Object Oriented VErification Copyright 2003--2007
 * University of Twente
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 *
 * $Id: ClosingStrategy.java 5914 2017-05-07 16:25:42Z rensink $
 */
package groove.explore.strategy;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;



import groove.explore.result.Acceptor;
import groove.grammar.QualName;
import groove.grammar.Rule;
import groove.grammar.aspect.AspectEdge;
import groove.grammar.host.HostEdge;
import groove.grammar.model.GrammarModel;
import groove.grammar.model.ResourceKind;
import groove.grammar.model.RuleModel;
import groove.grammar.rule.RuleEdge;
import groove.grammar.rule.RuleNode;
import groove.lts.GTS;
import groove.lts.GTSListener;
import groove.lts.GraphState;
import groove.lts.GraphTransition;
import groove.lts.MatchResult;
import groove.lts.RuleTransition;
import groove.lts.Status.Flag;
import groove.util.parse.FormatException;
import groove.verify.BaysianNetwork;
import groove.verify.BaysianNetwork.Node;
import groove.verify.ExploringGaBayesNet;
import groove.verify.ExploringItem;
import groove.verify.ExploringItem.NAC;
import groove.verify.ExploringItemIDA;
import groove.verify.ExploringItemPSO;
import groove.verify.Exploringinfo;
import groove.verify.LearningItem;

/**
 * Strategy that closes every state it explores, and adds the newly generated
 * states to a pool, together with information regarding the outgoing
 * transitions of its parent. Subclasses must decide on the order of the pool;
 * e.g., breadth-first or depth-first.
 */

abstract public class ClosingStrategy extends GTSStrategy {
    @Override
    public GraphState doNext() throws InterruptedException {
        GraphState state = getNextState();
        List<MatchResult> matches = state.getMatches();
        if (state.getActualFrame()
            .isTrial()) {
            //assert !state.isTransient();
            // there are potential rule matches now blocked until
            // the previous ones have been explored
            putInPool(state);
        }
        // explore known outgoing transitions of known states
        if (state.setFlag(Flag.KNOWN, false)) {
            for (RuleTransition out : state.getRuleTransitions()) {
                GraphState target = out.target();
                if (target.hasFlag(Flag.KNOWN)) {
                    addExplorable(target);
                }
            }
        }
        for (MatchResult next : matches) {
            state.applyMatch(next);
        }
        setNextState();
        return state;
    }
////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////BOA//////////BOA///////////////////////////////////////////////////////
////////////////////////BOA//////////BOA//////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////
    public GraphState heuristicBOAdoNext(ExploringGaBayesNet exploreGaBayesNet) {
	
    	if(exploreGaBayesNet.WhatStep.equals("CIP")){   //createInitialPopulation
    		createInitialPopulation_BOA(exploreGaBayesNet);
    	}
        	
    	if(exploreGaBayesNet.WhatStep.equals("SACFN")){// //Sampling_and_CalcFitness 
    													// Genetic & Learning of Baysian Networks Algoritms
    		sampling_Calc_Fitness_Population(exploreGaBayesNet);
    	}
    	if(exploreGaBayesNet.WhatStep.equals("CFN_Bayes")){  ////Try again with Simple GA 
    		calcfitness_Population(exploreGaBayesNet);
    	}
    	
    	return null;
    }

    private void createInitialPopulation_BOA(ExploringGaBayesNet exploreGaBayesNet){
    	
    	int maxLevelToExplore=exploreGaBayesNet.DepthOfSearch;
    	int CountOFpopulation=exploreGaBayesNet.CountOFpopulation;
    	
    	exploreGaBayesNet.tempStates.clear();
    	int chroindex=0;
    	while(chroindex<CountOFpopulation && heuristicResult==null){
    		exploreGaBayesNet.chroIndexCounterExamlpe=chroindex;
        	int mlevel=1;
        	GraphState initialState=null;
        	if(!exploreGaBayesNet.callFromHeuGenerator)
        		initialState=exploreGaBayesNet.simulator.getModel().getGTS().startState();
        	else
        		initialState=exploreGaBayesNet.initialState;
        	
        	transientStack.clear();
        	clearPool();
    		ExploringGaBayesNet.Chromosome chromosome=exploreGaBayesNet.getNewChromosome();
        	GraphState nextstate=null;
    		GraphState curstate=initialState;
    		exploreGaBayesNet.Call_Number_Fitness++;
    		while(curstate!=null && heuristicResult==null && mlevel<=maxLevelToExplore){
    			
    			ArrayList<String> seloutRulename=new ArrayList<String>();
    			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
    			
    			List<MatchResult> matches = curstate.getMatches();
    			
    			////////////////////////
				extend_size_tempStates(exploreGaBayesNet, curstate.getNumber());
				ExploringGaBayesNet.TempState tempstate=exploreGaBayesNet.tempStates.get(curstate.getNumber());
				if(tempstate.curstate==null){
					tempstate.curstate=curstate;
					tempstate.matches=matches;
					exploreGaBayesNet.Number_Explored_States++;
				}else if(matches.size()==0){
					matches=tempstate.matches;
					curstate=tempstate.curstate;
				}
				////////////////////////
    			if(matches.size()==0){
    				if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    				}
    				curstate=null;
    				break;
    			}else{
    				if(ISstateHasMCtargetGA_matches(exploreGaBayesNet, matches, exploreGaBayesNet.ModelCheckingTarget)){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    					curstate=null;
    					break;
    				}
    					
    			}
    			if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock"))
    				chromosome.fitness+=matches.size();
    				
    			for (MatchResult next : matches) {
    				String outRulename=next.toString();
    				if(outRulename.equals(exploreGaBayesNet.ModelCheckingTarget)){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    					curstate=null;
    					nextstate=null;
    					break;
    				}
    				if(!exploreGaBayesNet.Alltype.contains(outRulename)){
    					seloutRulename.add(outRulename);
    					selNext.add(next);
    				}
    			}
    			nextstate=null;
        		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
        			nextstate=null;
        			int x=-1;
        			String outRulename="";
    				while(!seloutRulename.isEmpty() && nextstate==null){
        				int n=seloutRulename.size();
    	    			Double d=Math.random()*n;
    	    			x=d.intValue();
    	    			outRulename=seloutRulename.get(x);
    	    			clearPool();
    	    			
    		        	RuleTransition ruletransition=null;
						try {
							ruletransition = curstate.applyMatch(selNext.get(x));
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}
    		        	setNextState();
        				nextstate=getNextState();
        				if(nextstate==null && ruletransition!=null && seloutRulename.size()==1){
        					nextstate=ruletransition.target();
        				}
    	    			
    					if(curstate.equals(nextstate))
    						nextstate=null;
    					if(nextstate==null && seloutRulename.size()==1){
    						for(int k=0;k<=tempstate.allRuleNames.size()-1;k++)
    							if(tempstate.allRuleNames.get(k).equals(outRulename)){
    								nextstate=tempstate.allNextStates.get(k);
    								break;
    							}
    					}else if(nextstate!=null){
    						tempstate.allRuleNames.add(outRulename);
            				tempstate.allNextStates.add(nextstate);	
    					}
    					seloutRulename.remove(x);
    					selNext.remove(x);
    				}
    				if(nextstate==null && tempstate.allRuleNames.size()>0){
    					int n=tempstate.allRuleNames.size();
    	    			Double d=Math.random()*n;
    	    			x=d.intValue();
    	    			outRulename=tempstate.allRuleNames.get(x);
    	    			nextstate=tempstate.allNextStates.get(x);
    				}
    				if(nextstate!=null){
    					chromosome.genes.add(x);
    					chromosome.ruleNames.add(outRulename);
    					chromosome.states.add(nextstate);
    					chromosome.lastState=nextstate;    //each step, is updated!!!
    					if(exploreGaBayesNet.maxValueInAllChromosomes<x)
    						exploreGaBayesNet.maxValueInAllChromosomes=x;
    				}
           		}  //end of if
        		mlevel++;
        		exploreGaBayesNet.tempStates.set(curstate.getNumber(), tempstate);
       			curstate=nextstate;
    		} //end of while
    		exploreGaBayesNet.heuristicResult=heuristicResult;
    		exploreGaBayesNet.First_Found_Dead_depth=mlevel-1;
    		
    		if(!exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){  
    			
    			
    			Set<? extends HostEdge> Host_edgeSet=null;
    			if(heuristicResult!=null && heuristicResult.equals("reachability"))
    				Host_edgeSet=exploreGaBayesNet.lastStateInReachability.getGraph().edgeSet();
    			else
    				Host_edgeSet=chromosome.lastState.getGraph().edgeSet();

            	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
            	for(HostEdge he:Host_edgeSet)
            		HedgeList.add(he);  
            	
             	ArrayList<String> HnodeList=new ArrayList<String>();
             	for(HostEdge he:Host_edgeSet)
         			if(!HnodeList.contains(he.source().toString())){
         				HnodeList.add(he.source().toString());
         			}
            	   	
             	
             	long startTime = System.currentTimeMillis();
             	chromosome.fitness=findEQU_GA(exploreGaBayesNet,HedgeList,HnodeList);
             	long reportTime= System.currentTimeMillis() - startTime;
             	exploreGaBayesNet.RunningTime_AllFitnessFuncs+=reportTime;
             	
             	if(heuristicResult!=null && heuristicResult.equals("reachability"))
             		exploreGaBayesNet.OPTValueOfFitness=chromosome.fitness;
             	
    		}
    		exploreGaBayesNet.population.add(chromosome);
    		exploreGaBayesNet.totalFitness+=chromosome.fitness;

    		chroindex++;
    	} //end of while
    	
		
    }
   
    private void sampling_Calc_Fitness_Population(ExploringGaBayesNet exploreGaBayesNet){
    	//int CountOFpopulation=exploreGaBayesNet.CountOFpopulation;
    	int CountOFpopulation=exploreGaBayesNet.population.size();
	   	
    	exploreGaBayesNet.tempStates.clear();
    	int chroindex=CountOFpopulation-exploreGaBayesNet.chroCountReplaceBySampling;
    	while(chroindex<CountOFpopulation && heuristicResult==null){
        	int gindex=0;  //gene index
        	exploreGaBayesNet.chroIndexCounterExamlpe=chroindex;
        	GraphState initialState=null;
        	if(!exploreGaBayesNet.callFromHeuGenerator)
        		initialState=exploreGaBayesNet.simulator.getModel().getGTS().startState();
        	else
        		initialState=exploreGaBayesNet.initialState;
        	transientStack.clear();
        	clearPool();
    		ExploringGaBayesNet.Chromosome chromosome=exploreGaBayesNet.population.get(chroindex);
    		
    		exploreGaBayesNet.Call_Number_Fitness++;
    		
    		int maxLevelToExplore=exploreGaBayesNet.DepthOfSearch;
    		chromosome.fitness=0;
    		chromosome.genes.clear();
    		chromosome.ruleNames.clear();
    		chromosome.states.clear();
    		
        	GraphState nextstate=null;
    		GraphState curstate=initialState;

			//String problemName= exploreGaBayesNet.simulator.getModel().getGts().getName().toString().toLowerCase();
			String curRulename="";
			String preRulename="";
    		String secondPreRulename="";
    		String thirdPreRulename="";
			String fourthPreRulename="";
    		
    		
    		while(curstate!=null && heuristicResult==null && gindex<maxLevelToExplore){
    			
    			fourthPreRulename=thirdPreRulename;
    			thirdPreRulename=secondPreRulename;
    			secondPreRulename=preRulename;
    			preRulename=curRulename;
    			
    			double maxprob=0;
    			ArrayList<String> selcurRulename=new ArrayList<String>();
    			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
    			List<MatchResult> matches = curstate.getMatches();
    			////////////////////////
				extend_size_tempStates(exploreGaBayesNet, curstate.getNumber());
				ExploringGaBayesNet.TempState tempstate=exploreGaBayesNet.tempStates.get(curstate.getNumber());
				if(tempstate.curstate==null){
					tempstate.curstate=curstate;
					tempstate.matches=matches;
					exploreGaBayesNet.Number_Explored_States++;
				}else{
					matches=tempstate.matches;
				}
				////////////////////////
    			if(matches.size()==0){
    				if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    				}
    				curstate=null;
    				break;
    			}else{
    				if(ISstateHasMCtargetGA_matches(exploreGaBayesNet, matches, exploreGaBayesNet.ModelCheckingTarget)){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    					curstate=null;
    					break;
    				}
    					
    			}
    			if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock"))
    				chromosome.fitness+=matches.size();
    				
    			for (MatchResult next : matches) {
    				curRulename=next.toString();
    				if(curRulename.equals(exploreGaBayesNet.ModelCheckingTarget)){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    					curstate=null;
    					nextstate=null;
    					break;
    				}
    				
    				double prob=0;
    				if(exploreGaBayesNet.BOAType.equals("naiveBOA"))
    					prob=findNaiveBayesProbabilityGA(exploreGaBayesNet, preRulename, curRulename);
    				else
    					prob=findBayesProbabilityGA(exploreGaBayesNet, fourthPreRulename,thirdPreRulename,secondPreRulename,preRulename,curRulename,gindex);
    				
    				
    			
    				
    				if(!exploreGaBayesNet.Alltype.contains(curRulename)){
	    				if(selcurRulename.size()==0){
	    					selcurRulename.add(curRulename);
	    					maxprob=prob;
	    					selNext.add(next);
	    				}else  if(prob==maxprob){
	    					selcurRulename.add(curRulename);
	    					maxprob=prob;
	    					selNext.add(next);
	    				}else if(prob>maxprob){
	    					selcurRulename.clear();
	    					selNext.clear();
	    					selcurRulename.add(curRulename);
	    					maxprob=prob;
	    					selNext.add(next);
	    				}
    				}
    				
    			}
    			nextstate=null;
        		if(selcurRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
        			nextstate=null;
        			int x=-1;
        			curRulename="";
    				while(!selcurRulename.isEmpty() && nextstate==null){
        				int n=selcurRulename.size();
    	    			Double d=Math.random()*n;
    	    			x=d.intValue();
    	    			curRulename=selcurRulename.get(x);
    	    			clearPool();
    	    			
    	    			RuleTransition ruletransition=null;
						try {
							ruletransition = curstate.applyMatch(selNext.get(x));
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}
    		        	setNextState();
        				nextstate=getNextState();
        				if(nextstate==null && ruletransition!=null && selcurRulename.size()==1){
        					nextstate=ruletransition.target();
        				}
    	    			
    	    			if(curstate.equals(nextstate))
    						nextstate=null;
    					if(nextstate==null && selcurRulename.size()==1){
    						for(int k=0;k<=tempstate.allRuleNames.size()-1;k++)
    							if(tempstate.allRuleNames.get(k).equals(curRulename)){
    								nextstate=tempstate.allNextStates.get(k);
    								break;
    							}
    					}else if(nextstate!=null){
    						tempstate.allRuleNames.add(curRulename);
            				tempstate.allNextStates.add(nextstate);	
    					}
    					selcurRulename.remove(x);
    					selNext.remove(x);
    				}
    				if(nextstate==null && tempstate.allRuleNames.size()>0){
    					int n=tempstate.allRuleNames.size();
    	    			Double d=Math.random()*n;
    	    			x=d.intValue();
    	    			curRulename=tempstate.allRuleNames.get(x);
    	    			nextstate=tempstate.allNextStates.get(x);
    				}
    				if(nextstate!=null){
    					chromosome.genes.add(x);
    					chromosome.ruleNames.add(curRulename);
    					chromosome.states.add(nextstate);
    					chromosome.lastState=nextstate;    //each step, is updated!!!
    					if(exploreGaBayesNet.maxValueInAllChromosomes<x)
    						exploreGaBayesNet.maxValueInAllChromosomes=x;
    				}
           		}  //end of if
        		gindex++;
        		exploreGaBayesNet.tempStates.set(curstate.getNumber(), tempstate);
       			curstate=nextstate;
    		} //end of while
    		exploreGaBayesNet.heuristicResult=heuristicResult;
    		exploreGaBayesNet.First_Found_Dead_depth=gindex;
    		
    		if(!exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){  
    			

    			Set<? extends HostEdge> Host_edgeSet=null;
    			if(heuristicResult!=null && heuristicResult.equals("reachability"))
    				Host_edgeSet=exploreGaBayesNet.lastStateInReachability.getGraph().edgeSet();
    			else
    				Host_edgeSet=chromosome.lastState.getGraph().edgeSet();


            	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
            	for(HostEdge he:Host_edgeSet)
            		HedgeList.add(he);  
            	
             	ArrayList<String> HnodeList=new ArrayList<String>();
             	for(HostEdge he:Host_edgeSet)
         			if(!HnodeList.contains(he.source().toString())){
         				HnodeList.add(he.source().toString());
         			}
            	   	
             	
             	long startTime = System.currentTimeMillis();
             	chromosome.fitness=findEQU_GA(exploreGaBayesNet,HedgeList,HnodeList);
             	long reportTime= System.currentTimeMillis() - startTime;
             	exploreGaBayesNet.RunningTime_AllFitnessFuncs+=reportTime;
             	if(heuristicResult!=null && heuristicResult.equals("reachability"))
             		exploreGaBayesNet.OPTValueOfFitness=chromosome.fitness;
    		}
    		exploreGaBayesNet.population.set(chroindex,chromosome);
    		exploreGaBayesNet.totalFitness+=chromosome.fitness;

    		chroindex++;
    	} //end of while
    	
        	
		
    }
    
    private void calcfitness_Population(ExploringGaBayesNet exploreGaBayesNet){
    	
    	int CountOFpopulation=exploreGaBayesNet.CountOFpopulation;
    	   	
    	exploreGaBayesNet.tempStates.clear();
    	int chroindex=0;
    	while(chroindex<CountOFpopulation && heuristicResult==null){
        	int gindex=0;  //gene index
        	exploreGaBayesNet.chroIndexCounterExamlpe=chroindex;
    		GraphState initialState=exploreGaBayesNet.simulator.getModel().getGTS().startState();
        	transientStack.clear();
        	clearPool();
    		ExploringGaBayesNet.Chromosome chromosome=exploreGaBayesNet.population.get(chroindex);
    		
    		int maxLevelToExplore=chromosome.genes.size();
    		
    		chromosome.fitness=0;
    		
			
        	GraphState nextstate=null;
    		GraphState curstate=initialState;

    		exploreGaBayesNet.Call_Number_Fitness++;
    		String problemName= exploreGaBayesNet.simulator.getModel().getGTS().getName().toString().toLowerCase();
    		
    		
    		while(curstate!=null && heuristicResult==null && gindex<maxLevelToExplore){
    			
    			
    			ArrayList<String> seloutRulename=new ArrayList<String>();
    			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
    			List<MatchResult> matches = curstate.getMatches();
    			////////////////////////
				extend_size_tempStates(exploreGaBayesNet, curstate.getNumber());
				ExploringGaBayesNet.TempState tempstate=exploreGaBayesNet.tempStates.get(curstate.getNumber());
				if(tempstate.curstate==null){
					tempstate.curstate=curstate;
					tempstate.matches=matches;
					exploreGaBayesNet.Number_Explored_States++;
				}else{
					matches=tempstate.matches;
				}
				////////////////////////
    			if(matches.size()==0){
    				if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    				}
    				curstate=null;
    				break;
    			}else{
    				if(ISstateHasMCtargetGA_matches(exploreGaBayesNet, matches, exploreGaBayesNet.ModelCheckingTarget)){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    					curstate=null;
    					break;
    				}
    					
    			}
    			if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock"))
    				chromosome.fitness+=matches.size();
    				
    			for (MatchResult next : matches) {
    				String outRulename=next.toString();
    				if(outRulename.equals(exploreGaBayesNet.ModelCheckingTarget)){
    					heuristicResult="reachability";
    					exploreGaBayesNet.lastStateInReachability=curstate;
    					curstate=null;
    					nextstate=null;
    					break;
    				}
    				
    				seloutRulename.add(outRulename);
    				selNext.add(next);
    			}
    			nextstate=null;
        		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
        			nextstate=null;
        			int x=-1;
        			String outRulename="";
        			int y=chromosome.genes.get(gindex);
        			if(y<seloutRulename.size()){
    	    			outRulename=seloutRulename.get(y);
    	    			clearPool();
    	    			
    	    			RuleTransition ruletransition=null;
						try {
							ruletransition = curstate.applyMatch(selNext.get(y));
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}
    		        	setNextState();
        				nextstate=getNextState();
        				if(nextstate==null && ruletransition!=null && seloutRulename.size()==1){
        					nextstate=ruletransition.target();
        				}
    	    			
    	    			   	    			
    					if(curstate.equals(nextstate))
    						nextstate=null;
    					seloutRulename.remove(y);
    					selNext.remove(y);
    	    			x=y;
        			}
        			while(!seloutRulename.isEmpty() && nextstate==null){
        				int n=seloutRulename.size();
    	    			Double d=Math.random()*n;
    	    			x=d.intValue();
    	    			outRulename=seloutRulename.get(x);
    	    			clearPool();
    	    			
    	    			RuleTransition ruletransition=null;
						try {
							ruletransition = curstate.applyMatch(selNext.get(x));
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}
    		        	setNextState();
        				nextstate=getNextState();
        				if(nextstate==null && ruletransition!=null && seloutRulename.size()==1){
        					nextstate=ruletransition.target();
        				}
    	    			    	    			
    					if(curstate.equals(nextstate))
    						nextstate=null;
    					if(nextstate==null && seloutRulename.size()==1 ){
    						for(int k=0;k<=tempstate.allRuleNames.size()-1;k++)
    							if(tempstate.allRuleNames.get(k).equals(outRulename)){
    								nextstate=tempstate.allNextStates.get(k);
    								break;
    							}
    					}else if(nextstate!=null){
    						tempstate.allRuleNames.add(outRulename);
            				tempstate.allNextStates.add(nextstate);	
    					}
    					seloutRulename.remove(x);
    					selNext.remove(x);
    				}
    				if(nextstate==null && tempstate.allRuleNames.size()>0){
    					int n=tempstate.allRuleNames.size();
    	    			Double d=Math.random()*n;
    	    			x=d.intValue();
    	    			outRulename=tempstate.allRuleNames.get(x);
    	    			nextstate=tempstate.allNextStates.get(x);
    				}
    				if(nextstate!=null){
    					chromosome.genes.set(gindex,x);
    					chromosome.ruleNames.add(outRulename);
    					chromosome.states.add(nextstate);
    					chromosome.lastState=nextstate;    //each step, is updated!!!
    					if(exploreGaBayesNet.maxValueInAllChromosomes<x)
    						exploreGaBayesNet.maxValueInAllChromosomes=x;
    				}
           		}  //end of if
        		gindex++;
        		exploreGaBayesNet.tempStates.set(curstate.getNumber(), tempstate);
       			curstate=nextstate;
    		} //end of while
    		exploreGaBayesNet.heuristicResult=heuristicResult;
    		exploreGaBayesNet.First_Found_Dead_depth=gindex;
    		
    		if(!exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){  
    			
    			Set<? extends HostEdge> Host_edgeSet=null;
    			if(heuristicResult!=null && heuristicResult.equals("reachability"))
    				Host_edgeSet=exploreGaBayesNet.lastStateInReachability.getGraph().edgeSet();
    			else
    				Host_edgeSet=chromosome.lastState.getGraph().edgeSet();


            	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
            	for(HostEdge he:Host_edgeSet)
            		HedgeList.add(he);  
            	
             	ArrayList<String> HnodeList=new ArrayList<String>();
             	for(HostEdge he:Host_edgeSet)
         			if(!HnodeList.contains(he.source().toString())){
         				HnodeList.add(he.source().toString());
         			}
           
             	
             	long startTime = System.currentTimeMillis();
             	chromosome.fitness=findEQU_GA(exploreGaBayesNet,HedgeList,HnodeList);
             	long reportTime= System.currentTimeMillis() - startTime;
             	exploreGaBayesNet.RunningTime_AllFitnessFuncs+=reportTime;
             	if(heuristicResult!=null && heuristicResult.equals("reachability"))
             		exploreGaBayesNet.OPTValueOfFitness=chromosome.fitness;
    		}
    		exploreGaBayesNet.population.set(chroindex,chromosome);
    		exploreGaBayesNet.totalFitness+=chromosome.fitness;

    		chroindex++;
    	} //end of while
    	
		
    }
    
    private double findBayesProbabilityGA(ExploringGaBayesNet exploreGaBayesNet,String fourthPreRulename,String thirdPreRulename,String secondPreRulename,String preRulename,String curRulename,int bayesNodeIndex){
    	   
    	double prob=0.0;
    	if(bayesNodeIndex<exploreGaBayesNet.baysNet.Nodes.size()){
	    	Node node=exploreGaBayesNet.baysNet.Nodes.get(bayesNodeIndex);
	    	for(int i=0;i<=node.NodeItems.size()-1;i++){
	    		if(node.NodeItems.get(i).curRulename.equals(curRulename) &&  node.NodeItems.get(i).prevRulename.equals(preRulename) && node.NodeItems.get(i).secondPrevRulename.equals(secondPreRulename) && node.NodeItems.get(i).thirdPrevRulename.equals(thirdPreRulename) && node.NodeItems.get(i).fourthPrevRulename.equals(fourthPreRulename))
	    			{prob=node.NodeItems.get(i).probability;break;}
	    	}
    	}
    	return prob;
    }
    private double findNaiveBayesProbabilityGA(ExploringGaBayesNet exploreGaBayesNet,String preRulename,String curRulename){
    	double prob=0.0;
    	BaysianNetwork.Node node;
    	if(preRulename.equals("")){
    		node=exploreGaBayesNet.baysNet.Nodes.get(0);
    		for(int i=0;i<=node.NodeItems.size()-1;i++){
        		if(node.NodeItems.get(i).curRulename.equals(curRulename)){
        			prob=node.NodeItems.get(i).probability;
        			break;
        		}
        	}
    	}
    	else{
    		node=exploreGaBayesNet.baysNet.Nodes.get(1);
    		for(int i=0;i<=node.NodeItems.size()-1;i++){
        		if(node.NodeItems.get(i).curRulename.equals(curRulename) &&  node.NodeItems.get(i).prevRulename.equals(preRulename))
        			{prob=node.NodeItems.get(i).probability;break;}
        	}
    	}
       	return prob;
    }

    
    private void extend_size_tempStates(ExploringGaBayesNet exploreGaBayesNet,int newIndex){
    	if(newIndex>exploreGaBayesNet.tempStates.size()-1){
    		for(int j=exploreGaBayesNet.tempStates.size();j<=newIndex;j++){
    			ExploringGaBayesNet.TempState tempState=exploreGaBayesNet.getNewTempState();
    			exploreGaBayesNet.tempStates.add(tempState);
    		}
    	}
    }
    
////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////Style///////////Style///////////////////////////////////////////////////////
////////////////////////Style///////////Style//////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

    public GraphState heuristicLEdoNext(ArrayList<LearningItem> ALearningItems,String ModelCheckingType,String ModelCheckingTarget,boolean isFirstStep) {

		////////////////////////////////
				
		ArrayList<QualName> Alltype=new ArrayList<QualName>();
		
		GrammarModel grammermodel=ALearningItems.get(0).simulator.getModel().getGrammar();
		
		Set<QualName> sname= grammermodel.getNames(ResourceKind.RULE);
       	Iterator<QualName> it=sname.iterator();
		
		
		while(it.hasNext()){
			QualName ts=it.next();
			RuleModel rulemodel=grammermodel.getRuleModel(ts);
			if(rulemodel.isEnabled()){
				Set<? extends AspectEdge> edgeSet=rulemodel.getSource().edgeSet();
			
				boolean flag=false;
				for(AspectEdge ae:edgeSet ){
					if(ae.toString().contains("new:") ||ae.toString().contains("del:")  ){
						flag=true;
						break;
					}
				}
				if(!flag){
					try{
						if(rulemodel.toResource().getAnchor().size()>0)
							flag=true;
					}
					catch (FormatException e) {
						// do nothing
						e.printStackTrace();
					}
				}
				
				if(!flag)
					Alltype.add(ts);
				}
		}
	
		ALearningItems.get(0).Alltype=Alltype;
	
		////////////////////////////

    	
    	
    	//////////////////////////////////////////////////////////
    	/////////////////////////////////////////////////////////
    	if(isFirstStep  && !ModelCheckingType.equals("RefuteLivenessByCycle")){
        	
    		GraphState initialState=getNextState();
        	GraphState state = initialState;
        	transientStack.clear();
        	clearPool();

    		
    		String problemName= ALearningItems.get(0).simulator.getModel().getGTS().getName().toString().toLowerCase();
    		int Maxrepeat=40;
    		
    		int repeat=1;

    		ArrayList<GraphState> allHCurState=new ArrayList<GraphState>();
    		ArrayList<String> allHRule=new ArrayList<String>();
    		ArrayList<GraphState> allHNextState=new ArrayList<GraphState>();
    		
    		
    		while(repeat<=Maxrepeat && heuristicResult==null){
	        	int Learn_index=0;
	        	while(heuristicResult==null && Learn_index<=ALearningItems.size()-1 ){
	        		state = initialState;
	        		boolean ischanged=true;
	        		while(ischanged){
	        			if(state==null)
	        				state=initialState;
	        			LearningItem  learningitem=ALearningItems.get(Learn_index);
	        			ischanged=false;
	        			for(int i=0  ;i<=learningitem.ExportedpatternNorepeat.size()-1 && heuristicResult==null && state!=null ;i++){
	            			String rulename=learningitem.ExportedpatternNorepeat.get(i);
	            			List<MatchResult> matches = state.getMatches();
	            			ALearningItems.get(0).Number_Explored_States++;
	            			if(ISstateHasMCtarget(ALearningItems,state, ModelCheckingTarget)){
	            				heuristicResult="reachability";
	            				ischanged=false;
	            				break;
	            			}else if(matches.size()==0){
	            				int rep=1;
	            				while(rep<=1000 &&  state.getMatches().size()==0){
	        		        		ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
	        		        		for(int u=0;u<=allHCurState.size()-1;u++)
	        		        			if(allHCurState.get(u).toString().equals(state.toString())
	        		        					&& allHRule.get(u).equals(rulename) )
	        		        				allstatet.add(allHNextState.get(u));
	        		        		     			
			        				int n=allstatet.size();
		    		    			Double d=Math.random()*n;
		    		    			int x=d.intValue();	
		    		    			GraphState statet;
		    		    			if(n>0)
		    		    				statet=allstatet.get(x);
		    		    			else
		    		    				statet=initialState;
	        		        		state=statet;
	        		        		rep++;
	            				}
	            				if(state.getMatches().size()==0)
	            					state=null;
	            				
	            				if(state!=null)
	            					ischanged=true;
	            				else
	            					ischanged=false;
	            				break;
	            			}
	            			ArrayList<String> seloutRulename=new ArrayList<String>();
	    					ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
	            			
	    					for (MatchResult next : matches) {
	        					if(next.toString().equals(rulename)){
	        						seloutRulename.add(rulename);
	    							selNext.add(next);
	        					}
	            			}
	    					if(seloutRulename.size()!=0 && selNext.size()!=0){
	        		        	int n=seloutRulename.size();
	    		    			Double d=Math.random()*n;
	    		    			int x=d.intValue();
	        		        	try {
									state.applyMatch(selNext.get(x));
								} catch (InterruptedException e) {
									// do nothing
									e.printStackTrace();
								}
	        		        	setNextState();
	            				GraphState statet=getNextState();
	            				ischanged=true;
	            				
	            				
	            				
	            				if(statet!=null){
		            				allHCurState.add(state);
		            				allHRule.add(seloutRulename.get(x));
		            				allHNextState.add(statet);
		            				
	            				}
	            				
	            				if(statet!=null && ISstateHasMCtarget(ALearningItems,statet, ModelCheckingTarget)){
	            					heuristicResult="reachability";
	                				ischanged=false;
	                				break;
	            				}
	        		        	if(statet!=null ){
	        		        		state=statet;
	        		        	}
	        		        	if(statet==null){
	        		        		ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
	        		        		for(int u=0;u<=allHCurState.size()-1;u++)
	        		        			if(allHCurState.get(u).toString().equals(state.toString())
	        		        					&& allHRule.get(u).equals(seloutRulename.get(x)) )
	        		        				allstatet.add(allHNextState.get(u));
	        		        		     			
    		        				n=allstatet.size();
    	    		    			d=Math.random()*n;
    	    		    			x=d.intValue();
    	    		    			if(n>0)
    	    		    				statet=allstatet.get(x);
    	    		    			else
    	    		    				statet=null;
	        		        		state=statet;
		        		       }
	        		        }///end if
	            		}//for
	        		} //while
	            	Learn_index++;
	        	}//while
	        	repeat++;
	    	}//while
    		
    		ALearningItems.get(0).heuristicResult=heuristicResult;
        	return null;
    	}////////end if
    	//////////////////////////////////////////////////////////////
		//////////////////////////////////////////////////////////
    	if(!isFirstStep && !ModelCheckingType.equals("RefuteLivenessByCycle") ){

    		int maxLevelToExplore=500;
    		int mlevel=1;
    		
    		GraphState initialState=getNextState();
        	GraphState state = initialState;
        	transientStack.clear();
        	clearPool();
    		
    		GraphState nextstate=null;
    		GraphState curstate=initialState;
    		
    		String preRuleName=null;
    		String nextRuleName=null;
    		
    		LearningItem learningItem=ALearningItems.get(0);
    		int i=1;
    		while(i<=ALearningItems.size()-1){
    			if(ALearningItems.get(i).allRulesNames.size()>learningItem.allRulesNames.size())
    				learningItem=ALearningItems.get(i);
    			i++;
    		}
    		
    		
    		while(curstate!=null && heuristicResult==null && mlevel<=maxLevelToExplore){
    			
    			
    			ArrayList<String> seloutRulename=new ArrayList<String>();
    			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
    			
    			preRuleName=nextRuleName;
    		
    			
    			List<MatchResult> matches = curstate.getMatches();
    			ALearningItems.get(0).Number_Explored_States++;
    			if(matches.size()==0 ){
    				if(ModelCheckingTarget.equals("DeadLock"))
    					heuristicResult="reachability";
    				curstate=null;
    				break;
    			}
    			if(ISstateHasMCtarget(ALearningItems,curstate, ModelCheckingTarget)){
    				heuristicResult="reachability";
    				curstate=null;
					nextstate=null;
					break;
    			}
    			for (MatchResult next : matches) {
    				String outRulename=next.toString();
    				if(outRulename.equals(ModelCheckingTarget)){
    					heuristicResult="reachability";
    					curstate=null;
    					nextstate=null;
    					break;
    				}
    				
    				nextRuleName=outRulename;
    				if(Is_exists_pre_next(learningItem, preRuleName, nextRuleName)){
    					seloutRulename.add(outRulename);
    					selNext.add(next);
    				}
    			}
    			nextstate=null;
        		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
        			nextstate=null;
        			while(!seloutRulename.isEmpty() && nextstate==null){
        				int n=seloutRulename.size();
    	    			Double d=Math.random()*n;
    	    			int x=d.intValue();
    	    			clearPool();
    	    			try {
							curstate.applyMatch(selNext.get(x));
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}
    	    			setNextState();
    					nextstate=getNextState();
    					nextRuleName=seloutRulename.get(x);
    					seloutRulename.remove(x);
    					selNext.remove(x);
    				}
        			
        			mlevel++;
       			}
        		curstate=nextstate;
    		} //end of while
    	}////end if
      	//////////////////////////////////////////////////////////////
    	//////////////////////////////////////////////////////////
    	if(ModelCheckingType.equals("RefuteLivenessByCycle")){
    		////go_hungry,get_forks,release_forks    startIndexofCycle=1
    		
    		
    		GraphState initialState=getNextState();
        	GraphState state = initialState;
        	transientStack.clear();
        	clearPool();

    		int Maxrepeat=40;
    		int repeat=1;

    		ArrayList<GraphState> allHCurState=new ArrayList<GraphState>();
    		ArrayList<String> allHRule=new ArrayList<String>();
    		ArrayList<GraphState> allHNextState=new ArrayList<GraphState>();
    		
    		
    		
    		while(repeat<=Maxrepeat && heuristicResult==null){
    			LearningItem learningitem=ALearningItems.get(0);
    			learningitem.pathLeadCycleInLargeModel.clear();
    			LearningItem.StateRule staterule=learningitem.getNewStateRule();
    			staterule.rule=null;
    			staterule.state=initialState;
    			learningitem.pathLeadCycleInLargeModel.add(staterule);
    			
    			
        		state = initialState;
        		
        		boolean isPropertyQsatisfied=false;
        		if(state==null)
    				state=initialState;
    			for(int i=0;i<=learningitem.ExportedpatternNorepeat.size()-1 && heuristicResult==null && state!=null ;i++){
        			String rulename=learningitem.ExportedpatternNorepeat.get(i);
        			List<MatchResult> matches = state.getMatches();
        			ALearningItems.get(0).Number_Explored_States++;
        			
        			for (MatchResult next : matches) {
        		        if(next.toString().equals(ModelCheckingTarget)){
        		        	isPropertyQsatisfied=true;
        		        	break;
        		        }
        		    }
        			if(isPropertyQsatisfied)
        				break;
        			
	        		if(matches.size()==0){
	        				ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
			        		for(int u=0;u<=allHCurState.size()-1;u++)
			        			if(allHCurState.get(u).toString().equals(state.toString())
			        					&& allHRule.get(u).equals(rulename) )
			        				allstatet.add(allHNextState.get(u));
			        		     			
	        				int n=allstatet.size();
			    			int x=(int)Math.random()*n;
			    			GraphState statet;
			    			if(n>0)
			    				statet=allstatet.get(x);
			    			else
			    				statet=null;
			        		state=statet;
			        		if(state!=null && !ALearningItems.get(0).Alltype.contains(rulename)){
			        			
			        			///////detect a cycle
			        			for(int j=1;j<=learningitem.pathLeadCycleInLargeModel.size()-1;j++){
			        				LearningItem.StateRule bstaterule=learningitem.pathLeadCycleInLargeModel.get(j);
			        				if(bstaterule.state.equals(state)){
			        					heuristicResult="reachability";
			        		        	break;
			        				}
			        			}
			        			if(heuristicResult=="reachability")
			        				break;
			        			///////////////
			        			
			        			staterule=learningitem.getNewStateRule();
			        			try {
									staterule.rule=(Rule) learningitem.simulator.getModel().getGrammar().getGraphResource(ResourceKind.RULE,QualName.name(rulename)).toResource();									
								} catch (FormatException e) {
								}
			        			staterule.state=state;
			        			learningitem.pathLeadCycleInLargeModel.add(staterule);
			        		}
	    		    }
    				if(state.getMatches().size()==0){
    					state=null;
    					break;
    				}
        			ArrayList<String> seloutRulename=new ArrayList<String>();
					ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
        			
					for (MatchResult next : matches) {
    					if(next.toString().equals(rulename)){
    						seloutRulename.add(rulename);
							selNext.add(next);
    					}
        			}
					if(seloutRulename.size()!=0 && selNext.size()!=0){
    		        	int n=seloutRulename.size();
		    			Double d=Math.random()*n;
		    			int x=d.intValue();
    		        	RuleTransition ruletransition=null;
						try {
							ruletransition = state.applyMatch(selNext.get(x));
						} catch (InterruptedException e1) {
							//do nothing
							e1.printStackTrace();
						}
    		        	setNextState();
        				GraphState statet=getNextState();
        				if(statet==null && ruletransition!=null){
        					statet=ruletransition.target();
        				}
        				
        				if(statet!=null){
            				allHCurState.add(state);
            				allHRule.add(seloutRulename.get(x));
            				allHNextState.add(statet);
            			}
        				
        				if(statet!=null && ISstateHasMCtarget(ALearningItems,statet, ModelCheckingTarget)){
        					isPropertyQsatisfied=true;
        		        	break;
        				}
    		        	if(statet!=null ){
    		        		state=statet;
    		        	}
    		        	if(statet==null){
    		        		ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
    		        		for(int u=0;u<=allHCurState.size()-1;u++)
    		        			if(allHCurState.get(u).toString().equals(state.toString())
    		        					&& allHRule.get(u).equals(seloutRulename.get(x)) )
    		        				allstatet.add(allHNextState.get(u));
    		        		     			
	        				n=allstatet.size();
    		    			d=Math.random()*n;
    		    			x=d.intValue();
    		    			if(n>0)
    		    				statet=allstatet.get(x);
    		    			else
    		    				statet=null;
    		        		state=statet;
        		       }
    		        	if(state!=null &&  !ALearningItems.get(0).Alltype.contains(rulename)  ){
    		        		
    		        		///////detect a cycle
		        			for(int j=1;j<=learningitem.pathLeadCycleInLargeModel.size()-1;j++){
		        				LearningItem.StateRule bstaterule=learningitem.pathLeadCycleInLargeModel.get(j);
		        				if(bstaterule.state.equals(state)){
		        					heuristicResult="reachability";
		        		        	break;
		        				}
		        			}
		        			if(heuristicResult!=null)
		        				break;
		        			///////////////
		        			
		        			
    		        		staterule=learningitem.getNewStateRule();
		        			try {
		        				staterule.rule=(Rule) learningitem.simulator.getModel().getGrammar().getGraphResource(ResourceKind.RULE,QualName.name(rulename)).toResource();
							} catch (FormatException e) {
							}
		        			staterule.state=state;
		        			learningitem.pathLeadCycleInLargeModel.add(staterule);
    		        	}
    		        }///end if
        		}//for
	        	repeat++;
	    	}//while

    	}
      	//////////////////////////////////////////////////////////////
    	/////////////////////////////////////////////////////////////
    	ALearningItems.get(0).heuristicResult=heuristicResult;
    	return null;
    
    }
    
	private  boolean ISstateHasMCtarget(ArrayList<LearningItem> ALearningItems,GraphState state,String ModelCheckingTarget ){
		boolean isexists=false;
		
		ArrayList<QualName> Alltype=ALearningItems.get(0).Alltype;
		
		List<MatchResult> matches=state.getMatches();
		boolean flag=true;
		if(ModelCheckingTarget.equals("DeadLock")){
			for (MatchResult next : matches) {
		        if(!Alltype.contains(QualName.name(next.toString()))){
		        	flag=false;
		        	break;
		        }
		        
		    }
			isexists=flag;

		}else{
			for (MatchResult next : matches) {
		        if(next.toString().equals(ModelCheckingTarget)){
		        	isexists=true;
		        	break;
		        }
		    }

		}
		
		
		
		return isexists;
	}



      private boolean Is_exists_pre_next(LearningItem learningItem ,String preRulename,String nextRulename){
    	if(preRulename==null)
    		return true;
    	
    	//[settleBill, payBill, BillGood, selectGood, BillGood, selectGood, createBill, takeCart]
    	
    	int i=learningItem.allRulesNames.size()-1;
    	while(i>=1){
    		if(learningItem.allRulesNames.get(i).equals(preRulename) && learningItem.allRulesNames.get(i-1).equals(nextRulename))
    			break;
    		i--;
    	}
    	if(i>=1)
    		return true;
    	else
    		return false;
    	
    
    }
////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////Explore until n nodes/////Learning From BFS////////////////////////////////////////////////////
////////////////////////Explore until n nodes/////Learning From BFS//////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////
      @SuppressWarnings("unchecked")
      public GraphState heuristicLearnFBFdoNext(ExploringItem exploringItems,int maxNumberOfStates,boolean isLearningStep) {
            	
            	int depthOfSearch=100;  //for example /// using for BFS 
            	////////////////////////////////////////////////////////////////////////////
            	////////////////////deadlock & reachability////////////////
            	if(isLearningStep && !exploringItems.CTLproperty.equals("liveByCycle") && !exploringItems.CTLproperty.equals("liveByDeadlock")){
            		exploringItems.allcurStates.clear();
        			exploringItems.allcurStatesOutDegree.clear();
        			exploringItems.allcurStatesNames.clear();
                	exploringItems.allcurdepth.clear();
                	exploringItems.allEQU_Count.clear();
                	exploringItems.State_Max_EQU=null;
                	exploringItems.allpath_From_S0_To_Max.clear();
                	exploringItems.allpath_From_S0_To_Max_fitness.clear();
                	exploringItems.Exportedpattern=null;
                	exploringItems.ExportedpatternNorepeat.clear();
                	
            		      		
            		GraphState initialState=getNextState();   //get from poll
            		GraphState state = initialState;
                	transientStack.clear();
                	clearPool();
                	
                	ArrayList<GraphState> curList=new ArrayList<GraphState>();
                	ArrayList<GraphState> nextList=new ArrayList<GraphState>();
                	
                	nextList.add(state);
                	
                	int numberOfState=1;
                	int curDepth=0;
                	while(curDepth<depthOfSearch && numberOfState<maxNumberOfStates && exploringItems.heuristicResult==null){
                		curList=(ArrayList<GraphState>)nextList.clone();
                		if(curList.isEmpty())
                			break;
                		nextList.clear();
                		for(int i=0;i<=curList.size()-1 && numberOfState<maxNumberOfStates && exploringItems.heuristicResult==null ;i++){
      	          			state=curList.get(i);
      	          			
      	          			exploringItems.allcurStates.add(state);
      	          			exploringItems.allcurStatesOutDegree.add(state.getMatches().size());
      	          			exploringItems.allcurStatesNames.add(state.toString());
      	                  	exploringItems.allcurdepth.add(curDepth);
      	                  	exploringItems.allEQU_Count.add(0);
                        	
        						List<MatchResult> matches = state.getMatches();
        						
        						if(ISstateHasMCtarget_FBFS(exploringItems,state)){
        							exploringItems.heuristicResult="reachability";
              					exploringItems.First_Found_Dead_depth=curDepth;
                					exploringItems.lastStateInReachability=state;
                					break;
        						}
        							
        						  						
                        		for (MatchResult next : matches){
	      	                  	  	if(next.toString().equals(exploringItems.targetRule)){
	      	                  			exploringItems.heuristicResult="reachability";
	      	                  			exploringItems.First_Found_Dead_depth=curDepth;
	      	                  			exploringItems.lastStateInReachability=state;
	      	                  			break;
	      	                  		}
	      	                  		try {
										state.applyMatch(next);
									} catch (InterruptedException e) {
										// do nothing
										e.printStackTrace();
									}            //call putInPool(resultState)
	      	                  		GraphState statet=getFromPool();   //return this.stateQueue.poll()
	      	                  		if(statet!=null){
	      	                  			nextList.add(statet);
	      	                  			numberOfState++;
	      	                  			if(numberOfState>=maxNumberOfStates){
	      	                  				for(int j=i+1;j<=curList.size()-1;j++){
	      	  	            					state=curList.get(j);
	      	  	                    			
	      	  	                    			exploringItems.allcurStates.add(state);
	      	  	                    			exploringItems.allcurStatesOutDegree.add(state.getMatches().size());
	      	  	                    			exploringItems.allcurStatesNames.add(state.toString());
	      	  	                            	exploringItems.allcurdepth.add(curDepth);
	      	  	                            	exploringItems.allEQU_Count.add(0);
	      	  	                            	
	      	  	                          	} //end of for
	      	                  				for(int j=0;j<=nextList.size()-1;j++){
	      	  	            					state=nextList.get(j);
	      	  	                    			
	      	  	                    			exploringItems.allcurStates.add(state);
	      	  	                    			exploringItems.allcurStatesOutDegree.add(state.getMatches().size());
	      	  	                    			exploringItems.allcurStatesNames.add(state.toString());
	      	  	                            	exploringItems.allcurdepth.add(curDepth+1);
	      	  	                            	exploringItems.allEQU_Count.add(0);
	      	  	                            	
	                        					}
	                        					break;
	                        				} //end of if
	                        			}
                        		} //end of for
                   		}//end of for
                			curDepth++;
                   	}//end of while
               	exploringItems.Number_Explored_States+=exploringItems.allcurStates.size();
                	
                	if(exploringItems.heuristicResult!=null)
                		return null;
                	
                	exploringItems.State_Max_EQU=null;
                	int count=0;
                	if(exploringItems.CTLproperty.equals("reachability") || exploringItems.CTLproperty.equals("safetyByReach")){
      	          	for(int i=0;i<=exploringItems.allcurStates.size()-1;i++){
      	    			state=exploringItems.allcurStates.get(i);
      	    			if(exploringItems.allcurdepth.get(i)==curDepth && Math.random()<=0.1){ 
      		            	count++;
      	    				Set<? extends HostEdge> Host_edgeSet=state.getGraph().edgeSet();
      		            	  
      		            	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
      		            	for(HostEdge he:Host_edgeSet)
      		            		HedgeList.add(he);  
      		            	
      		             	ArrayList<String> HnodeList=new ArrayList<String>();
      		             	for(HostEdge he:Host_edgeSet)
      		         			if(!HnodeList.contains(he.source().toString())){
      		         				HnodeList.add(he.source().toString());
      		         			}
      		            	   	
      		            	exploringItems.allEQU_Count.set(i,findEQU(exploringItems,HedgeList,HnodeList));
      		             	
      		            	if(exploringItems.State_Max_EQU==null){
      		            		exploringItems.State_Max_EQU=state;
      		            		exploringItems.Max_EQU=exploringItems.allEQU_Count.get(i);
      		            	}else{
      		            		if(exploringItems.allEQU_Count.get(i)>exploringItems.Max_EQU){
      		            			exploringItems.State_Max_EQU=state;
      		            			exploringItems.Max_EQU=exploringItems.allEQU_Count.get(i);
      		            		}
      		            	}
      	    			}
      	      		
      	            } //end of for
      	          	
      	          	//try again to obtain a State_Max_EQU state
      	          	if(exploringItems.State_Max_EQU==null){
      	          		curDepth--;
      	          		for(int i=0;i<=exploringItems.allcurStates.size()-1;i++){
      		    			state=exploringItems.allcurStates.get(i);
      		    			if(exploringItems.allcurdepth.get(i)==curDepth && Math.random()<=0.2){ 
      			            	count++;
      		    				Set<? extends HostEdge> Host_edgeSet=state.getGraph().edgeSet();
      			            	  
      			            	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
      			            	for(HostEdge he:Host_edgeSet)
      			            		HedgeList.add(he);  
      			            	
      			             	ArrayList<String> HnodeList=new ArrayList<String>();
      			             	for(HostEdge he:Host_edgeSet)
      			         			if(!HnodeList.contains(he.source().toString())){
      			         				HnodeList.add(he.source().toString());
      			         			}
      			            	   	
      			            	exploringItems.allEQU_Count.set(i,findEQU(exploringItems,HedgeList,HnodeList));
      			             	
      			            	if(exploringItems.State_Max_EQU==null){
      			            		exploringItems.State_Max_EQU=state;
      			            		exploringItems.Max_EQU=exploringItems.allEQU_Count.get(i);
      			            	}else{
      			            		if(exploringItems.allEQU_Count.get(i)>exploringItems.Max_EQU){
      			            			exploringItems.State_Max_EQU=state;
      			            			exploringItems.Max_EQU=exploringItems.allEQU_Count.get(i);
      			            		}
      			            	}
      		    			}
      		      		
      		            } //end of for
      	          	}
                	}

                	///////////////
                	
                	exploringItems.maxDepthOfSearch=curDepth;
                	
        	 	
                	

                	////////////////////////////////////////////////////////////////
                	
                	if(exploringItems.CTLproperty.equals("deadlock")){
                		exploringItems.maxNum_allPathFs0TMax=500;
                		findAllPathFs0Trand_dead(exploringItems);
                	}
                	else if(exploringItems.CTLproperty.equals("reachability") || exploringItems.CTLproperty.equals("safetyByReach")){
                		exploringItems.maxNum_allPathFs0TMax=100;
                		findAllPathFs0Tmax_reach(exploringItems);
                	}
                	/////////////////////////////////////////////////////////////////
                 
      			/////////////////////
                	if(exploringItems.typeOfLearn.equals("BN"))
                		LearnOfNaiveBaysianNetwork(exploringItems);
                	else{
                		 ////remove all extra rules
                		
                		exploringItems.orig_allpath_From_S0_To_Max=(ArrayList<String>) exploringItems.allpath_From_S0_To_Max.clone();
                		
          			for(int i=0;i<=exploringItems.allpath_From_S0_To_Max.size()-1;i++){
          				String[] s=exploringItems.allpath_From_S0_To_Max.get(i).split(",");
          				String t="";
          				for(int w=0;w<=s.length-1;w++){
          					if(!t.contains(s[w])){
          						t+=","+s[w];
          					}
          				}
          				exploringItems.allpath_From_S0_To_Max.set(i, t.substring(1));
          			}
          			
                		FindFreqPatt_Apriori(exploringItems, exploringItems.minsup);
                	}
                	          	
                	return null;
              }
      		
            	//////////////////////////////////////////////////////////////////////
            	///////////////////////liveByCycle////////////////////////////////////
            	if(isLearningStep && exploringItems.CTLproperty.equals("liveByCycle")){
            		
            		exploringItems.allpath_From_S0_To_Max.clear();
            		
            		
            	 
              	int maxLevelToExplore=300;
              	exploringItems.tempStates.clear();
              	while(exploringItems.Number_Explored_States<exploringItems.maxNumberOfStates && exploringItems.heuristicResult==null){
              		int mlevel=1;
                  	GraphState initialState=null;
                  	
                  	if(!exploringItems.callFromHeuGenerator)
                  		initialState=exploringItems.simulator.getModel().getGTS().startState();
                  	else
                  		initialState=exploringItems.initialState;

                  	        	
                  	transientStack.clear();
                  	clearPool();
              		String path="";
                  	GraphState nextstate=null;
              		GraphState curstate=initialState;
              		
              		String outRulename="";
              		
              		
              		exploringItems.pathLeadCycle.clear();
            			ExploringItem.StateRule staterule=exploringItems.getNewStateRule();
            			staterule.rule=null;
            			staterule.state=curstate;
            			exploringItems.pathLeadCycle.add(staterule);
              		
              		
              		while(curstate!=null && mlevel<=maxLevelToExplore && exploringItems.heuristicResult==null  && exploringItems.Number_Explored_States<exploringItems.maxNumberOfStates){
              			
              			ArrayList<String> seloutRulename=new ArrayList<String>();
              			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
              			
              			List<MatchResult> matches = curstate.getMatches();
              			exploringItems.Number_Explored_States++;
              			////////////////////////
          				extend_size_tempStates_FBF(exploringItems, curstate.getNumber());
          				ExploringItem.TempState tempstate=exploringItems.tempStates.get(curstate.getNumber());
          				if(tempstate.curstate==null){
          					tempstate.curstate=curstate;
          					tempstate.matches=matches;
          				}else if(matches.size()==0){
          					matches=tempstate.matches;
          					curstate=tempstate.curstate;
          				}
          				////////////////////////
              			if(matches.size()==0){
              				curstate=null;
              				break;
              			}else{
              				if(ISstateHasMCtarget_FBFS(exploringItems,curstate)){
              					path=path.substring(1);
                      			exploringItems.allpath_From_S0_To_Max.add(path);
              					path="";
              					curstate=null;
              					break;
              				}
              			}
              			
              			for (MatchResult next : matches) {
              				outRulename=next.toString();
              				if(outRulename.equals(exploringItems.targetRule)){
              					path=path.substring(1);
                      			exploringItems.allpath_From_S0_To_Max.add(path);
              					path="";
              					curstate=null;
              					nextstate=null;
              					break;
              				}else{
              					seloutRulename.add(outRulename);
              					selNext.add(next);
              				}
              			}
              			nextstate=null;
                  		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
                  			nextstate=null;
                  			int x=-1;
                  			outRulename="";
              				while(!seloutRulename.isEmpty() && nextstate==null){
                  				int n=seloutRulename.size();
              	    			Double d=Math.random()*n;
              	    			x=d.intValue();
              	    			outRulename=seloutRulename.get(x);
              	    			clearPool();
              	    			
              		        	RuleTransition ruletransition=null;
								try {
									ruletransition = curstate.applyMatch(selNext.get(x));
								} catch (InterruptedException e) {
									// do nothing
									e.printStackTrace();
								}
              		        	setNextState();
                  				nextstate=getNextState();
                  				if(nextstate==null && ruletransition!=null && seloutRulename.size()==1){
                  					nextstate=ruletransition.target();
                  				}
              	    			
                  				
                  				if(exploringItems.Number_Explored_States>=exploringItems.maxNumberOfStates)
                  					break;
                  				
              					if(curstate.equals(nextstate))
              						nextstate=null;
              					if(nextstate==null && seloutRulename.size()==1){
              						for(int k=0;k<=tempstate.allRuleNames.size()-1;k++)
              							if(tempstate.allRuleNames.get(k).equals(outRulename)){
              								nextstate=tempstate.allNextStates.get(k);
              								break;
              							}
              					}else if(nextstate!=null){
              						tempstate.allRuleNames.add(outRulename);
                      				tempstate.allNextStates.add(nextstate);	
              					}
              					seloutRulename.remove(x);
              					selNext.remove(x);
              				}
              				if(nextstate==null && tempstate.allRuleNames.size()>0){
              					int n=tempstate.allRuleNames.size();
              	    			Double d=Math.random()*n;
              	    			x=d.intValue();
              	    			outRulename=tempstate.allRuleNames.get(x);
              	    			nextstate=tempstate.allNextStates.get(x);
              				}
              				if(nextstate!=null)
              					path=path+","+outRulename;
              				
                     		}  //end of if
                  		
                  		
      	      			if(nextstate!=null && !ISstateHasMCtarget_FBFS(exploringItems,nextstate)){
      	      				///////detect a cycle
      	        			for(int j=0;j<=exploringItems.pathLeadCycle.size()-1 && exploringItems.pathLeadCycle.size()>=2 ;j++){
      	        				ExploringItem.StateRule bstaterule=exploringItems.pathLeadCycle.get(j);
      	        				if(bstaterule.state.equals(nextstate)){
      	        					exploringItems.heuristicResult="reachability";
      	        					exploringItems.First_Found_Dead_depth=exploringItems.pathLeadCycle.size();
      	        					exploringItems.lastStateInReachability=nextstate;
      	        		        	break;
      	        				}
      	        			}
      	        			if(exploringItems.heuristicResult!=null)
      	        				break;
      	        			///////////////
      	        			
      	        			
      		        		staterule=exploringItems.getNewStateRule();
      	        			try {
      							staterule.rule=(Rule)exploringItems.grammermodel.getGraphResource(ResourceKind.RULE, QualName.name(outRulename)).toResource();
      						} catch (FormatException e) {
      						}
      	        			staterule.state=nextstate;
      	        			exploringItems.pathLeadCycle.add(staterule);
      	      			}
                  		
                  		
                  		
                  		
                  		
                  		mlevel++;
                  		exploringItems.tempStates.set(curstate.getNumber(), tempstate);
                 			curstate=nextstate;
              		} //end of while
              		
              		if(path!=""){
              			path=path.substring(1);
              			exploringItems.allpath_From_S0_To_Max.add(path);
              		}
              	} //end of while

                	/////////////////////////////////////////////////////////////////
                	
              	reviseAllPathFs0T_live(exploringItems);
              	
              	
                	if(exploringItems.typeOfLearn.equals("BN"))
                		LearnOfNaiveBaysianNetwork(exploringItems);
                	else
                		FindFreqPatt_Apriori(exploringItems, exploringItems.minsup);
                	/////////////////////////////////////////////////////////////////
                
                	
                	
                	return null;
              }
            	//////////////////////////////////////////////////////////////////////
            	///////////////////////liveByDeadlock////////////////////////////////////
            	if(isLearningStep && exploringItems.CTLproperty.equals("liveByDeadlock")){
            		exploringItems.allcurStates.clear();
        			exploringItems.allcurStatesOutDegree.clear();
        			exploringItems.allcurStatesNames.clear();
                	exploringItems.allcurdepth.clear();
                	exploringItems.allEQU_Count.clear();
                	exploringItems.State_Max_EQU=null;
                	exploringItems.allpath_From_S0_To_Max.clear();
                	exploringItems.allpath_From_S0_To_Max_fitness.clear();
                	exploringItems.Exportedpattern=null;
                	exploringItems.ExportedpatternNorepeat.clear();
                	
            		      		
            		GraphState initialState=getNextState();   //get from poll
                	GraphState state = initialState;
                	transientStack.clear();
                	clearPool();
                	
                	ArrayList<GraphState> curList=new ArrayList<GraphState>();
                	ArrayList<GraphState> nextList=new ArrayList<GraphState>();
                	
                	nextList.add(state);
                	
                	int numberOfState=1;
                	int curDepth=0;
                	while(curDepth<depthOfSearch && numberOfState<maxNumberOfStates && exploringItems.heuristicResult==null){
                		curList=(ArrayList<GraphState>)nextList.clone();
                		if(curList.isEmpty())
                			break;
                		nextList.clear();
                		for(int i=0;i<=curList.size()-1 && numberOfState<maxNumberOfStates && exploringItems.heuristicResult==null ;i++){
      	          			state=curList.get(i);
      	          			
      	          			exploringItems.allcurStates.add(state);
      	          			exploringItems.allcurStatesOutDegree.add(state.getMatches().size());
      	          			exploringItems.allcurStatesNames.add(state.toString());
      	                  	exploringItems.allcurdepth.add(curDepth);
      	                  	exploringItems.allEQU_Count.add(0);
      	                  	
      	                  	
        						List<MatchResult> matches = state.getMatches();
        						
        						if(ISstateHasMCtarget_FBFS(exploringItems,state)){
        			  				exploringItems.heuristicResult="reachability";
        							exploringItems.First_Found_Dead_depth=curDepth-1;
        							exploringItems.lastStateInReachability=state;
        							break;
        						}
        						
        						
        						  						
                        		for (MatchResult next : matches){
      	                  	  	try {
									state.applyMatch(next);
								} catch (InterruptedException e) {
									// do nothing
									e.printStackTrace();
								}            //call putInPool(resultState)
      	                  		GraphState statet=getFromPool();   //return this.stateQueue.poll()
      	                  		if(statet!=null){
      	                  			nextList.add(statet);
      	                  			numberOfState++;
      	                  			if(numberOfState>=maxNumberOfStates){
      	                  				for(int j=i+1;j<=curList.size()-1;j++){
      	  	            					state=curList.get(j);
      	  	                    			
      	  	                    			exploringItems.allcurStates.add(state);
      	  	                    			exploringItems.allcurStatesOutDegree.add(state.getMatches().size());
      	  	                    			exploringItems.allcurStatesNames.add(state.toString());
      	  	                            	exploringItems.allcurdepth.add(curDepth);
      	  	                            	exploringItems.allEQU_Count.add(0);
      	  	                            	
      	  	                          	} //end of for
      	                  				for(int j=0;j<=nextList.size()-1;j++){
      	  	            					state=nextList.get(j);
      	  	                    			
      	  	                    			exploringItems.allcurStates.add(state);
      	  	                    			exploringItems.allcurStatesOutDegree.add(state.getMatches().size());
      	  	                    			exploringItems.allcurStatesNames.add(state.toString());
      	  	                            	exploringItems.allcurdepth.add(curDepth+1);
      	  	                            	exploringItems.allEQU_Count.add(0);
      	  	                            	
                        					}
                        					break;
                        				} //end of if
                        			}
                        		} //end of for
                   		}//end of for
                			curDepth++;
                   	}//end of while
                	
                	
               	exploringItems.Number_Explored_States=exploringItems.allcurStates.size();
                	
                	exploringItems.maxDepthOfSearch=curDepth;
                	////////////////////////////////////////////////////////////////
                	
                	if(exploringItems.CTLproperty.equals("liveByDeadlock")){
                		exploringItems.maxNum_allPathFs0TMax=500;
                		findAllPathFs0Trand_LivebyDead(exploringItems);
                	}
                	
                	/////////////////////////////////////////////////////////////////
                 
      			/////////////////////
                	if(exploringItems.typeOfLearn.equals("BN"))
                		LearnOfNaiveBaysianNetwork(exploringItems);
                	else{
                		 ////remove all extra rules
          			for(int i=0;i<=exploringItems.allpath_From_S0_To_Max.size()-1;i++){
          				String[] s=exploringItems.allpath_From_S0_To_Max.get(i).split(",");
          				String t="";
          				for(int w=0;w<=s.length-1;w++){
          					if(!t.contains(s[w])){
          						t+=","+s[w];
          					}
          				}
          				exploringItems.allpath_From_S0_To_Max.set(i, t.substring(1));
          			}
          			
                		FindFreqPatt_Apriori(exploringItems, exploringItems.minsup);
                	}
                	          	
                	return null;
              
            	}
            	
            	
            	//////////////////////////////////////////////////////////////////////
            	//////////////////////////////////////////////////////////////////////
            	/////////////////////////////////////////////////////////////////////
            	/////////isLearningStep=false/////////////////////////////////////////////////////////////
            	////////////////////////////////////////////
            	if(exploringItems.typeOfLearn.equals("DM"))   //data mining
            		return heuLearnDMdoNext(exploringItems);
            	/////////////////////////////////////////////
            	////////////////////////////////////////////
            	////////Bayesian Network////////////////////
        		
        		Set<? extends GraphState> nodeset=exploringItems.gtsLearning.nodeSet();
        		Set<? extends GraphTransition> edgeset=exploringItems.gtsLearning.edgeSet();
        		
        		 		
        		if(!exploringItems.CTLproperty.equals("liveByCycle")){
      	  		GraphState curstate=exploringItems.initialState;
      	  		String preRulename="";
      	  		String curRulename="";
      	  		
      	  		exploringItems.State_Max_EQU=exploringItems.initialState;
      	  		curstate=exploringItems.State_Max_EQU;
      	  		
      	  		exploringItems.Number_Explored_States++;
      	  		int maxLevelToExplore=exploringItems.maxDepth;
      	  		int mlevel=1;
      	  		
      	  		GraphState nextstate=null;
      	  		while(curstate!=null && exploringItems.heuristicResult==null && mlevel<=maxLevelToExplore){
      	  			double maxprob=0;
      	  			ArrayList<String> selcurRulename=new ArrayList<String>();
      	  			ArrayList<Double> selcurRuleProb=new ArrayList<Double>();
      	  			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
      	  			
      	  		
      	  			
      	  			List<MatchResult> matches = curstate.getMatches();
      	  			
      	  			if(matches.size()==0 ){
      					curstate=null;
      					nextstate=null;
      	  				break;
      				}
      	  			
      	  			
      	  			if(exploringItems.CTLproperty.equals("liveByDeadlock")){
              			for (MatchResult next : matches) {
          	  				curRulename=next.toString();
          	  				if(curRulename.equals(exploringItems.targetRule)){
          	  					curstate=null;
                  				break;
          	  				}
          	  			}
          			}
      	  			
      	  			if(curstate==null)
      	  				break;
      				
      	  			if(ISstateHasMCtarget_FBFS(exploringItems,curstate)){
      	  				exploringItems.heuristicResult="reachability";
      					exploringItems.First_Found_Dead_depth=mlevel-1;
      					exploringItems.lastStateInReachability=curstate;
      					curstate=null;
      					nextstate=null;
      					break;
      				}
      	  			
      	  			
      	  			for (MatchResult next : matches) {
      	  				curRulename=next.toString();
      	  				if(curRulename.equals(exploringItems.targetRule)){
      	  					exploringItems.heuristicResult="reachability";
      	  					exploringItems.First_Found_Dead_depth=mlevel-1;
      	  					exploringItems.lastStateInReachability=curstate;
      	  					curstate=null;
      	  					nextstate=null;
      	  					break;
      	  				}
      	  				
      	  			
      	  				double prob=findNaiveBayesProb(exploringItems, preRulename, curRulename);
      	  				
      	  				if(selcurRulename.size()==0){
      	  					selcurRulename.add(curRulename);
      	  					maxprob=prob;
      	  					selNext.add(next);
      	  				}else  if(prob==maxprob){
      	  					selcurRulename.add(curRulename);
      	  					maxprob=prob;
      	  					selNext.add(next);
      	  				}else if(prob>maxprob){
      	  					selcurRulename.clear();
      	  					selNext.clear();
      	  					selcurRulename.add(curRulename);
      	  					maxprob=prob;
      	  					selNext.add(next);
      	  				}
      	  			}
      	  			
      				
      		  			if(selcurRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
      		      			nextstate=null;
      		      			while(!selcurRulename.isEmpty() && nextstate==null){
      		      				int n=selcurRulename.size();
      		  	    			Double d=Math.random()*n;
      		  	    			int x=d.intValue();
      		    				curRulename=selcurRulename.get(x);
      		  	    			clearPool();
      		  	    			try {
									curstate.applyMatch(selNext.get(x));
								} catch (InterruptedException e) {
									//do nothing
									e.printStackTrace();
								}
      		  	    			preRulename=selcurRulename.get(x);
      		  		        	setNextState();
      		  					nextstate=getNextState();
      		  					selcurRulename.remove(x);
      		  					selNext.remove(x);
      		  				}
      		      			mlevel++;
      		      			exploringItems.Number_Explored_States++;
      	     			}
      	      		curstate=nextstate;
      	  		} //end of while
      	
      	  		return null;
        		}
        		if(exploringItems.CTLproperty.equals("liveByCycle")){
      	  		GraphState curstate=exploringItems.initialState;
      	  		String preRulename="";
      	  		String curRulename="";
      	  		
      	  		exploringItems.Number_Explored_States++;
      	  		int maxLevelToExplore=exploringItems.maxDepth;;
      	  		int mlevel=1;
      	  		
      	  		
      	  		
      	  		exploringItems.pathLeadCycle.clear();
        			ExploringItem.StateRule staterule=exploringItems.getNewStateRule();
        			staterule.rule=null;
        			staterule.state=curstate;
        			exploringItems.pathLeadCycle.add(staterule);
      	  		
        			boolean isPropertyQsatisfied=false;
        			
      	  		GraphState nextstate=null;
      	  		while(curstate!=null && exploringItems.heuristicResult==null && mlevel<=maxLevelToExplore){
      	  			double maxprob=0;
      	  			ArrayList<String> selcurRulename=new ArrayList<String>();
      	  			ArrayList<Double> selcurRuleProb=new ArrayList<Double>();
      	  			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
      	  			
      	  			
      	  			
      	  			
      	  			List<MatchResult> matches = curstate.getMatches();
      	  			
      	  			if(matches.size()==0 ){
      					curstate=null;
      					nextstate=null;
      	  				break;
      				}
      				
      	  			if(ISstateHasMCtarget_FBFS(exploringItems,curstate)){
      	  				isPropertyQsatisfied=true;
      		        	curstate=null;
      					nextstate=null;
      					break;
      				}
      	  			
      	  			for (MatchResult next : matches) {
      	  				curRulename=next.toString();
      	  				if(curRulename.equals(exploringItems.targetRule)){
      	  					isPropertyQsatisfied=true;
      	  					curstate=null;
      	  					nextstate=null;
      	  					break;
      	  				}
      	  					  			
      	  				double prob=findNaiveBayesProb(exploringItems, preRulename, curRulename);
      	  				
      	  				if(selcurRulename.size()==0){
      	  					selcurRulename.add(curRulename);
      	  					maxprob=prob;
      	  					selNext.add(next);
      	  				}else  if(prob==maxprob){
      	  					selcurRulename.add(curRulename);
      	  					maxprob=prob;
      	  					selNext.add(next);
      	  				}else if(prob>maxprob){
      	  					selcurRulename.clear();
      	  					selNext.clear();
      	  					selcurRulename.add(curRulename);
      	  					maxprob=prob;
      	  					selNext.add(next);
      	  				}
      	  			}
      	  			
      				
      		  		 if(selcurRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
      		      			nextstate=null;
      		      			while(!selcurRulename.isEmpty() && nextstate==null){
      		      				int n=selcurRulename.size();
      		  	    			Double d=Math.random()*n;
      		  	    			int x=d.intValue();
      		    				curRulename=selcurRulename.get(x);
      		  	    			clearPool();
      		  	    			RuleTransition ruletransition=null;
								try {
									ruletransition = curstate.applyMatch(selNext.get(x));
								} catch (InterruptedException e) {
									// do nothing
									e.printStackTrace();
								}
      		  	    			preRulename=selcurRulename.get(x);
      		  		        	setNextState();
      		  					nextstate=getNextState();
      		  					if(nextstate==null && ruletransition!=null){
      		  						nextstate=ruletransition.target();
      		  					}
      		  					selcurRulename.remove(x);
      		  					selNext.remove(x);
      		  				}
      		      			exploringItems.Number_Explored_States++;
      		      			if(nextstate!=null && !ISstateHasMCtarget_FBFS(exploringItems,nextstate)){
      		      				///////detect a cycle
      		        			for(int j=0;j<=exploringItems.pathLeadCycle.size()-1 && exploringItems.pathLeadCycle.size()>=2 ;j++){
      		        				ExploringItem.StateRule bstaterule=exploringItems.pathLeadCycle.get(j);
      		        				if(bstaterule.state.equals(nextstate)){
      		        					exploringItems.heuristicResult="reachability";
      		        					exploringItems.First_Found_Dead_depth=exploringItems.pathLeadCycle.size();
      		        					exploringItems.lastStateInReachability=nextstate;
      		        		        	break;
      		        				}
      		        			}
      		        			if(exploringItems.heuristicResult!=null)
      		        				break;
      		        			///////////////
      		        			
      		        			
      			        		staterule=exploringItems.getNewStateRule();
      		        			try {
      								//staterule.rule=(Rule)exploringItems.simulator.getModel().getGrammar().getGraphResource(ResourceKind.RULE, curRulename).toResource();
      		        				staterule.rule=(Rule)exploringItems.grammermodel.getGraphResource(ResourceKind.RULE,QualName.name(curRulename)).toResource();
      							} catch (FormatException e) {
      							}
      		        			staterule.state=nextstate;
      		        			exploringItems.pathLeadCycle.add(staterule);
      		      			}
      	     		}
      		  		curstate=nextstate;
      	  		} //end of while
      	
      	  		return null;
        		}
     	return null;
     }
      
      private void extend_size_tempStates_FBF(ExploringItem exploringItems,int newIndex){
      	if(newIndex>exploringItems.tempStates.size()-1){
      		for(int j=exploringItems.tempStates.size();j<=newIndex;j++){
      			ExploringItem.TempState tempState=exploringItems.getNewTempState();
      			exploringItems.tempStates.add(tempState);
      		}
      	}
      }
      
      ////////////////////////////////////////////////////
      private int findEQU(ExploringItem exploringItems,ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList){

      	ArrayList<RuleEdge> TedgeList=exploringItems.targetGraph_edgeList;
      	ArrayList<RuleNode> TnodeList=exploringItems.targetGraph_nodeList;
      	
      	///////////////////////////////////////////////////////////////
      	/////////////////////////////find positive equality////////////
      	//////////////////////////////////////////////////////////////
      	exploringItems.allinfo.clear();
      	for(int i=0;i<=TnodeList.size()-1;i++)    
      		for(int j=0;j<=HnodeList.size()-1;j++) {   
  	    		Exploringinfo  einfo=new Exploringinfo();
      			einfo.tnode=TnodeList.get(i).toString();
      			einfo.hnode=HnodeList.get(j).toString();
      			exploringItems.allinfo.add(einfo);
  	        }
  	      
      	for(int i=0;i<=exploringItems.allinfo.size()-1;i++){
      		Exploringinfo  einfo=exploringItems.allinfo.get(i);
      		String tn=einfo.tnode;
      		String hn=einfo.hnode;
      		int equall_count=0;
      		int tnode_edges_count=0;
      		
      		ArrayList<String> hedges=new ArrayList<String>();
      		
      		for(int k=0;k<=TedgeList.size()-1;k++){
      			RuleEdge ae=TedgeList.get(k);
      			if(ae.source().toString().equals(tn)){
      				tnode_edges_count++;
      				String tlabel=ae.label().toString();
      				for(int p=0;p<=HedgeList.size()-1;p++){
      					HostEdge he=HedgeList.get(p);
      					if(he.source().toString().equals(hn) && he.label().toString().equals(tlabel) && !hedges.contains(he.toString()))
      					{equall_count++;hedges.add(he.toString());break;}
      				}
      			}
      		}
      		einfo.equall_count=equall_count;
      		einfo.tnode_edges_count=tnode_edges_count;
      		einfo.diff=tnode_edges_count-equall_count;
      		if(einfo.diff==0 && i<exploringItems.allinfo.size()-1){
      			int j=i+1;
      			Exploringinfo  einfoo=exploringItems.allinfo.get(j);
      			while(j<=exploringItems.allinfo.size()-1){
      				if((einfoo.hnode.equals(hn) || einfoo.tnode.equals(tn) )){
      					exploringItems.allinfo.remove(j);
      					j=j;
      				}else
      					j++;
      				if(j<=exploringItems.allinfo.size()-1)
      					einfoo=exploringItems.allinfo.get(j);
      			}
      		}
      	}
      	
      	///////////////////////////////bubble sort///
      	///sort based on equall_count Descending (from greater to smaller)
      	
      	boolean swapped = true;
      	int p = 0;
      	Exploringinfo  tmp;
      	while (swapped){
      		swapped = false;
              p++;
              for (int i = 0; i < exploringItems.allinfo.size() - p; i++) {
              		if (exploringItems.allinfo.get(i).equall_count < exploringItems.allinfo.get(i+1).equall_count) {
                            tmp = exploringItems.allinfo.get(i);
                            exploringItems.allinfo.set(i, exploringItems.allinfo.get(i+1));
                            exploringItems.allinfo.set(i+1,tmp);
                            swapped = true;
                      }
                }
          }
      	//////////////////////////////
      	ArrayList<String> tnodes=new ArrayList<String>();
      	ArrayList<String> hnodes=new ArrayList<String>();
      	int EQU_Count=0;
      	for(int i=0;i<=exploringItems.allinfo.size()-1;i++){
      		Exploringinfo  einfo=exploringItems.allinfo.get(i);
      		String tn=einfo.tnode;
      		String hn=einfo.hnode;
      		if(!tnodes.contains(tn) && !hnodes.contains(hn)){
      			tnodes.add(tn);
      			hnodes.add(hn);
      			EQU_Count+=einfo.equall_count;
      		}
      	}
      		
      	
      	///////////////////////////////////////////////////////////////
      	/////////////////////////////find negative equality////////////
      	///////////////////////////////////////////////////////////////
      	if(exploringItems.allNACs==null)
      		return EQU_Count;
      	int NegEQU_Count=0;
      	@SuppressWarnings("unchecked")
  		ArrayList<NAC> allNACs= (ArrayList<NAC>)exploringItems.allNACs.clone();
      	for(int i=0;i<=exploringItems.allNACs.size()-1;i++){
      		searchNacEquallNodes(HedgeList, HnodeList, exploringItems, i);
      		ExploringItem.NAC nac=allNACs.get(i);
      		if(nac.ANacEqualNodes.size()==0)
      			continue;
      		ArrayList<RuleNode> tnodeList=new ArrayList<RuleNode>();
      		for(int j=0;j<=nac.ruleedgeList.size()-1;j++){
      			RuleEdge tEdge=nac.ruleedgeList.get(j);
      			RuleNode tNode=tEdge.source();
      			if(tEdge.isLoop() && isSingleNode(nac,tNode) && !tnodeList.contains(tNode)){
      				int tIndex=IndexOfNodeInANac(nac, tNode);
      				NegEQU_Count+=nac.ANacEqualNodes.get(tIndex).HEList.size();
      				tnodeList.add(tNode);
      			}else if(!tEdge.isLoop()){
      				RuleNode tNodeSource=tEdge.source();
      				RuleNode tNodeTarget=tEdge.target();
      				tnodeList.add(tNodeSource);
      				if(tNodeTarget.toString().contains("bool")){
      					int tSourceIndex=IndexOfNodeInANac(nac, tNodeSource);
  	    				NegEQU_Count+=nac.ANacEqualNodes.get(tSourceIndex).HEList.size();
      				}else{
  	    				tnodeList.add(tNodeTarget);
  	    				int tSourceIndex=IndexOfNodeInANac(nac, tNodeSource);
  	    				if(tSourceIndex==-1)
  	    					continue;
  	    				int tTargetIndex=IndexOfNodeInANac(nac, tNodeTarget);
  	    				if(tTargetIndex==-1)
  	    					continue;
  	    				ExploringItem.NacEqualNode tSourceEqualNode=nac.ANacEqualNodes.get(tSourceIndex);
  	    				ExploringItem.NacEqualNode tTargetEqualNode=nac.ANacEqualNodes.get(tTargetIndex);
  	    				for(int k=0;k<=tSourceEqualNode.HEList.size()-1;k++){
  	    					String hNodeSource=tSourceEqualNode.HEList.get(k);
  	    					for(int q=0;q<=tTargetEqualNode.HEList.size()-1;q++){
  	    						String hNodeTarget=tTargetEqualNode.HEList.get(q);
  	    						if(isExistsEdgeWithLabel(HedgeList,hNodeSource, hNodeTarget, tEdge.label().toString())){
  	    							NegEQU_Count++;
  	    						}
  	    					}
  	    				}
      				}
      			}
      		}
      		
      	
      	}
         	////////////////////////////////////////////////
       	return EQU_Count-NegEQU_Count;
      }

      
      private boolean isExistsEdgeWithLabel(ArrayList<HostEdge>  HedgeList,String hNodeSource,String hNodeTarget,String label){
      	for(int i=0;i<=HedgeList.size()-1;i++){
      		HostEdge hEdge=HedgeList.get(i);
      		if(hEdge.source().toString().equals(hNodeSource) && hEdge.target().toString().equals(hNodeTarget) && hEdge.label().toString().equals(label))
      			return true;
      	}
      	return false;
      }
      private void searchNacEquallNodes(ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList,ExploringItem exploringItems,int NacIndex){
      	ExploringItem.NAC nac=exploringItems.allNACs.get(NacIndex);
      	nac.ANacEqualNodes.clear();
      	for(int i=0;i<=nac.rulenodeList.size()-1;i++){
      		ExploringItem.NacEqualNode nacEqualNode=null;
      		RuleNode tNode=nac.rulenodeList.get(i);
      		if(tNode.toString().contains("bool"))
      			continue;
      		for(int j=0;j<=HnodeList.size()-1;j++){
      			String hNode=HnodeList.get(j);
      			boolean isContinue=true;
      			for(int k=0;k<=nac.ruleedgeList.size()-1 && isContinue;k++){
          			RuleEdge tEdge=nac.ruleedgeList.get(k);
          			if(tEdge.isLoop() && tEdge.source().equals(tNode)){
          				boolean isFind=false;
          				for(int p=0;p<=HedgeList.size()-1;p++){
          					HostEdge hEdge=HedgeList.get(p);
          					if(hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode)){
          						isFind=true;
          						break;
          					}
          				}
          				isContinue=isFind;
          			}else if(!tEdge.isLoop() && tEdge.source().equals(tNode) && tEdge.target().toString().contains("bool")){
          				boolean isFind=false;
          				for(int p=0;p<=HedgeList.size()-1;p++){
          					HostEdge hEdge=HedgeList.get(p);
          					if(!hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode) && hEdge.target().toString().contains(tEdge.target().toString())){
          						isFind=true;
          						break;
          					}
          				}
          				isContinue=isFind;
          			}
      			}
      			if(isContinue){
      				if(nacEqualNode==null)
      					nacEqualNode=exploringItems.getNewNacEqualNode();
      				nacEqualNode.tNode=tNode;
      				nacEqualNode.HEList.add(hNode);
      			}
      		}
      		if(nacEqualNode!=null)
      			nac.ANacEqualNodes.add(nacEqualNode);
      	}
      	exploringItems.allNACs.set(NacIndex,nac);    	
      }
      private boolean isSingleNode(ExploringItem.NAC nac,RuleNode tNode){
      	boolean isSingle=true;
      	for(int q=0;q<=nac.ruleedgeList.size()-1;q++){
  			RuleEdge tEdge=nac.ruleedgeList.get(q);
  			if(!tEdge.isLoop() && (tEdge.source().equals(tNode) || tEdge.target().equals(tNode))){
  				isSingle=false;
  				break;
  			}
  		}
      	return isSingle;
      }
   
      private int IndexOfNodeInANac(ExploringItem.NAC nac,RuleNode tNode){
        	for(int i=0;i<=nac.ANacEqualNodes.size()-1;i++)
      		if(nac.ANacEqualNodes.get(i).tNode.equals(tNode)){
      			return i;
      		}
      	return -1;
      }
////////////////////
      private double findNaiveBayesProb(ExploringItem exploringItems,String preRulename,String curRulename){
      	double prob=0.0;
      	BaysianNetwork.Node node;
      	if(preRulename.equals("")){
      		node=exploringItems.baysNet.Nodes.get(0);
      		for(int i=0;i<=node.NodeItems.size()-1;i++){
          		if(node.NodeItems.get(i).curRulename.equals(curRulename)){
          			prob=node.NodeItems.get(i).probability;
          			break;
          		}
          	}
      	}
      	else{
      		node=exploringItems.baysNet.Nodes.get(1);
      		for(int i=0;i<=node.NodeItems.size()-1;i++){
          		if(node.NodeItems.get(i).curRulename.equals(curRulename) &&  node.NodeItems.get(i).prevRulename.equals(preRulename))
          			{prob=node.NodeItems.get(i).probability;break;}
          	}
      	}
         	return prob;
      }
/////////////////////////////////////////////
/////////////////////////////////////////////
      
    private void findAllPathFs0Tmax_reach(ExploringItem exploringItems){
    	///find all paths from s0 to State_Max_EQU
    	
		exploringItems.allpath_From_S0_To_Max.clear();
		GTS gts=null;
		if(exploringItems.callFromHeuGenerator)
			gts=exploringItems.gts;
		else
			gts =exploringItems.simulator.getModel().getGTS();
		
		Set<? extends GraphState> nodeset=gts.nodeSet();
		Set<? extends GraphTransition> edgeset=gts.edgeSet();
		
		
		
		GraphState oriState=exploringItems.State_Max_EQU;
		
		dfs(exploringItems.State_Max_EQU, "",0, exploringItems, exploringItems.grammermodel, nodeset);
    	
    	findOtherState_Max_EQU(exploringItems);
    	
    	if(exploringItems.State_Max_EQU!=null && !oriState.equals(exploringItems.State_Max_EQU)){
    		oriState=exploringItems.State_Max_EQU;
    		dfs(exploringItems.State_Max_EQU, "",0, exploringItems, exploringItems.grammermodel, nodeset);
    	}
    	
    	findOtherState_Max_EQU(exploringItems);
    	if(exploringItems.State_Max_EQU!=null && !oriState.equals(exploringItems.State_Max_EQU)){
    		oriState=exploringItems.State_Max_EQU;
    		dfs(exploringItems.State_Max_EQU, "",0, exploringItems, exploringItems.grammermodel, nodeset);
    	}	
    	    	
    }
    /////////////////////////////////////////
    private void findAllPathFs0Trand_dead(ExploringItem exploringItems){
    	///find all paths from s0 to some random states in the last depth
    	
		exploringItems.allpath_From_S0_To_Max.clear();
		
		GTS gts =null;
		
		if(exploringItems.callFromHeuGenerator)
			gts=exploringItems.gts;
		else
			gts =exploringItems.simulator.getModel().getGTS();
		
		Set<? extends GraphState> nodeset=gts.nodeSet();
		Set<? extends GraphTransition> edgeset=gts.edgeSet();
		
		
		
		
		int i=0;
		while (i<=exploringItems.allcurdepth.size()-1 && exploringItems.allcurdepth.get(i)<exploringItems.maxDepthOfSearch)
			i++;
		int low=i;
		int high=exploringItems.allcurdepth.size()-1;
		int rep=0;
		
		int numPromis=50;   //for example 50
		
		while(rep<=numPromis){   
			Double x=Math.random();
			i=(int)((high-low)*x+low);
			GraphState oriState=exploringItems.allcurStates.get(i);
			
			dfs(oriState, "", 0,exploringItems, exploringItems.grammermodel, nodeset);
			rep++;
		}
		 
		
		
		///////////////////////////////bubble sort///
		///sort allpath_From_S0_To_Max based on allpath_From_S0_To_Max_fitness Ascending (from smaller to greater)
		
		boolean swapped = true;
		int p = 0;
		String  tmpS;
		Integer tmpI;
		while (swapped){
			swapped = false;
			p++;
			for ( i = 0; i < exploringItems.allpath_From_S0_To_Max.size() - 1; i++) {
				if (exploringItems.allpath_From_S0_To_Max_fitness.get(i)> exploringItems.allpath_From_S0_To_Max_fitness.get(i+1)) {
				      tmpS = exploringItems.allpath_From_S0_To_Max.get(i);
				      exploringItems.allpath_From_S0_To_Max.set(i, exploringItems.allpath_From_S0_To_Max.get(i+1));
				      exploringItems.allpath_From_S0_To_Max.set(i+1,tmpS);
				      
				      tmpI = exploringItems.allpath_From_S0_To_Max_fitness.get(i);
				      exploringItems.allpath_From_S0_To_Max_fitness.set(i, exploringItems.allpath_From_S0_To_Max_fitness.get(i+1));
				      exploringItems.allpath_From_S0_To_Max_fitness.set(i+1,tmpI);
				      
				      swapped = true;
				}
			}
		}
		/////////////////////
		//Remove all additional items and only some items will be remained	
		while(exploringItems.allpath_From_S0_To_Max.size()>40){
			exploringItems.allpath_From_S0_To_Max.remove(40);
			exploringItems.allpath_From_S0_To_Max_fitness.remove(40);
		}
				    	
    }  
    /////////////////////////////////////////
    private void findAllPathFs0Trand_LivebyDead(ExploringItem exploringItems){
    	///find all paths from s0 to some random states in the last depth
    	
		exploringItems.allpath_From_S0_To_Max.clear();
		
		GTS gts =null;
		if(exploringItems.callFromHeuGenerator)
			gts=exploringItems.gts;
		else
			gts =exploringItems.simulator.getModel().getGTS();
		
		Set<? extends GraphState> nodeset=gts.nodeSet();
		Set<? extends GraphTransition> edgeset=gts.edgeSet();
		
		
		
		
		int i=0;
		while (i<=exploringItems.allcurdepth.size()-1 && exploringItems.allcurdepth.get(i)<exploringItems.maxDepthOfSearch)
			i++;
		int low=i;
		int high=exploringItems.allcurdepth.size()-1;
		int rep=0;
		
		int numPromis=50;   //for example 50
		
		while(rep<=numPromis){   
			Double x=Math.random();
			i=(int)((high-low)*x+low);
			GraphState oriState=exploringItems.allcurStates.get(i);
			
			Boolean isPropertyQsatisfied=false;
			for (MatchResult next : oriState.getMatches()) {
  				String curRulename=next.toString();
  				if(curRulename.equals(exploringItems.targetRule)){
  					isPropertyQsatisfied=true;
  					break;
  				}
			}	 
			if(!isPropertyQsatisfied){
				dfs(oriState, "", 0,exploringItems, exploringItems.grammermodel, nodeset);
				rep++;
			}
		}
		
		///////////////////////////////bubble sort///
		///sort allpath_From_S0_To_Max based on allpath_From_S0_To_Max_fitness Ascending (from smaller to greater)
		
		boolean swapped = true;
		int p = 0;
		String  tmpS;
		Integer tmpI;
		while (swapped){
			swapped = false;
			p++;
			for ( i = 0; i < exploringItems.allpath_From_S0_To_Max.size() - 1; i++) {
				if (exploringItems.allpath_From_S0_To_Max_fitness.get(i)> exploringItems.allpath_From_S0_To_Max_fitness.get(i+1)) {
				      tmpS = exploringItems.allpath_From_S0_To_Max.get(i);
				      exploringItems.allpath_From_S0_To_Max.set(i, exploringItems.allpath_From_S0_To_Max.get(i+1));
				      exploringItems.allpath_From_S0_To_Max.set(i+1,tmpS);
				      
				      tmpI = exploringItems.allpath_From_S0_To_Max_fitness.get(i);
				      exploringItems.allpath_From_S0_To_Max_fitness.set(i, exploringItems.allpath_From_S0_To_Max_fitness.get(i+1));
				      exploringItems.allpath_From_S0_To_Max_fitness.set(i+1,tmpI);
				      
				      swapped = true;
				}
			}
		}
		/////////////////////
		//Remove all additional items and only some items will be remained	
		while(exploringItems.allpath_From_S0_To_Max.size()>40){
			exploringItems.allpath_From_S0_To_Max.remove(40);
			exploringItems.allpath_From_S0_To_Max_fitness.remove(40);
		}
				    	
    }  
    
    ////////
    /////////////////////////////////////////
    private void reviseAllPathFs0T_live(ExploringItem exploringItems){
    	///revise all paths from s0 
    	
    	for(int i=0;i<=exploringItems.allpath_From_S0_To_Max.size()-1;i++){
    		String path=exploringItems.allpath_From_S0_To_Max.get(i);
    		String[] s=path.split(",");
    		for(int j=0;j<=s.length-1;j++)
    			if(s[j]!=""){
    				for(int k=j+1;k<=s.length-1;k++){
    					if(s[j].equals(s[k]))
    						s[k]="";
    				}
    			} 
    		path="";
    		for(int j=0;j<=s.length-1;j++)
    			if(s[j]!="")
    				path=path+","+s[j];
    		path=path.substring(1);
    		exploringItems.allpath_From_S0_To_Max.set(i,path);
        } 
		///////////////////////////////bubble sort///
		///sort allpath_From_S0_To_Max on their path length 
		
		boolean swapped = true;
		int p = 0;
		String  tmpS;
		Integer tmpI;
		while (swapped){
			swapped = false;
			p++;
			for (int i = 0; i < exploringItems.allpath_From_S0_To_Max.size() - 1; i++) {
				if (exploringItems.allpath_From_S0_To_Max.get(i).length()<exploringItems.allpath_From_S0_To_Max.get(i+1).length()) {
				      tmpS = exploringItems.allpath_From_S0_To_Max.get(i);
				      exploringItems.allpath_From_S0_To_Max.set(i, exploringItems.allpath_From_S0_To_Max.get(i+1));
				      exploringItems.allpath_From_S0_To_Max.set(i+1,tmpS);
				      
				      swapped = true;
				}
			}
		}
		/////////////////////
		//Remove all additional items and only some items will be remained	
		while(exploringItems.allpath_From_S0_To_Max.size()>10){  //for example 10
			exploringItems.allpath_From_S0_To_Max.remove(10);
		}

    	
    }
        
/////////////////////////////////////////////
/////////////////////////////////////////////      
    private void LearnOfNaiveBaysianNetwork(ExploringItem exploringItems){
	      	
    	
    	 ///////////////////////////////////////////////
    	////For Learning of Naive Bayes Network
	    ////Rule_current--->Rule_next 
    	////////////////////////////////////////	
    	exploringItems.baysNet.Nodes.clear();
	  		
    	if(exploringItems.allpath_From_S0_To_Max.size()==0)
    		return;
	  		
  		///add the first node 
      	BaysianNetwork.Node curnode=exploringItems.baysNet.getNewNode();
      	for(int i=0;i<=exploringItems.RulesCount-1;i++){
      		BaysianNetwork.Nodeitem nodeitem=exploringItems.baysNet.getNewNodeitem();
      		nodeitem.curRulename=exploringItems.RulesName.get(i).toString();
      		nodeitem.prevRulename="";
      		curnode.NodeItems.add(nodeitem);
      	}
      	exploringItems.baysNet.Nodes.add(curnode);
      	
      	//add the next nodes
      	BaysianNetwork.Node nextnode=exploringItems.baysNet.getNewNode();
      	for(int i=0;i<=exploringItems.RulesCount-1;i++)
      		for(int j=0;j<=exploringItems.RulesCount-1;j++){
      			BaysianNetwork.Nodeitem nodeitem=exploringItems.baysNet.getNewNodeitem();
      			nodeitem.curRulename=exploringItems.RulesName.get(i).toString();
          		nodeitem.prevRulename=exploringItems.RulesName.get(j).toString();
          		nextnode.NodeItems.add(nodeitem);
      		}
      	exploringItems.baysNet.Nodes.add(nextnode);
      	
      	
      	String curRulename="";
      	String prevRulename="";
      	
      	//[go-hungry, get-left, go-hungry, get-left]
      	
      	for(int k=0;k<=exploringItems.baysNet.Nodes.size()-1;k++){
  			BaysianNetwork.Node node=exploringItems.baysNet.Nodes.get(k);
  			for(int r=0;r<=node.NodeItems.size()-1;r++){
  				BaysianNetwork.Nodeitem nodeitem=node.NodeItems.get(r);
  				curRulename=nodeitem.curRulename;
  				prevRulename=nodeitem.prevRulename;
  				int count=0;
  				if(k==0){///////////Make The First Node (CurrentNode)////prevRulename==""/////////////////////////////////////
  					for(int i=0;i<=exploringItems.allpath_From_S0_To_Max.size()-1;i++){
  						//path="go-hungry,get-left,get-right,go-hungry,"
  	      				String[] path=exploringItems.allpath_From_S0_To_Max.get(i).split(",");
  						for(int j=0;j<=path.length-2;j++)
  		    				if(curRulename.equals(path[j]))
  		    					count++;
  		 			}
  					nodeitem.probability=(double)count/(exploringItems.allpath_From_S0_To_Max.size() * (exploringItems.allpath_From_S0_To_Max.get(0).length())-1);
  				}else {  ////////Make NextNode ////////////
  					int count_pre=0;  //#(X0=prevRulename)
  					for(int i=0;i<=exploringItems.allpath_From_S0_To_Max.size()-1;i++){
  						String[] path=exploringItems.allpath_From_S0_To_Max.get(i).split(",");
  						for(int j=1;j<=path.length-1;j++)
  							if(prevRulename.equals(path[j-1])){
  		    					count_pre++;
  		    					if(curRulename.equals(path[j]))
  		    						count++;
  		    				}
  		 			}
  					nodeitem.probability=(double)count/count_pre; //#(X1=curRulename|X0=prevRulename)/#(X0=prevRulename)
  				}
  			}  ////end of for
  			exploringItems.baysNet.Nodes.set(k,node);
      	} ///end of for
  		
  	  }
        
/////////////////////////////////////////////
/////////////////////////////////////////////
    @SuppressWarnings({ "unchecked", "unused" })
	private void FindFreqPatt_Apriori(ExploringItem exploringItem,double minsup){
		
    	
    	
    	ArrayList<String>  allpath=new ArrayList<String>();
		
    	////revise allpath////
    	for(int i=0;i<=exploringItem.allpath_From_S0_To_Max.size()-1;i++){
    		String t=exploringItem.allpath_From_S0_To_Max.get(i);
    		String[] a=t.split(",");
    		Boolean flag=false;
    		for(int j=0;j<=a.length-2 && !flag;j++)
    			for(int k=j+1;k<=a.length-1 && !flag;k++)
    				if(!a[j].equals(a[k])){
    					flag=true;
    				}
    		if(flag)
    			allpath.add(t);
    	}
    	if(allpath.size()==0)
    		allpath.add(exploringItem.allpath_From_S0_To_Max.get(0));
    	
    	
		////make C_1
		
		String[] s=allpath.get(0).split(",");
		if(exploringItem.C1_Items.size()==0){
			for(int i=0;i<=s.length-1;i++){
				boolean flag=false;
				for(int j=0;j<=exploringItem.C1_Items.size()-1;j++){
					if(exploringItem.C1_Items.get(j).rules.equals(s[i]))
					{flag=true;break;}
				}
				if(!flag){
					ExploringItem.Item item=exploringItem.getNewItem();
					item.rules=s[i];
					exploringItem.C1_Items.add(item);
				}
			}
			for(int i=0;i<=exploringItem.C1_Items.size()-1;i++){
				String p=exploringItem.C1_Items.get(i).rules.toString();
				exploringItem.C1_Items.get(i).support=findsupport2(allpath, p);
			}
		}
		
		//////////////////////
		exploringItem.CK_Items=(ArrayList<ExploringItem.Item>)exploringItem.C1_Items.clone();
		
		for(int k=1;exploringItem.CK_Items.size()>0;k++){
		
			//////////////make C_k+1
			exploringItem.Ctemp_Items.clear();
			for(int i=0;i<=exploringItem.CK_Items.size()-1;i++)
				for(int j=0;j<=exploringItem.C1_Items.size()-1;j++){
					if(!exploringItem.CK_Items.get(i).rules.contains(exploringItem.C1_Items.get(j).rules)){
						ExploringItem.Item item=exploringItem.getNewItem();
						item.rules=exploringItem.CK_Items.get(i).rules+","+exploringItem.C1_Items.get(j).rules;
						exploringItem.Ctemp_Items.add(item);
					}
				}
			for(int i=0;i<=exploringItem.Ctemp_Items.size()-1;i++){
				String p=exploringItem.Ctemp_Items.get(i).rules.toString();
				exploringItem.Ctemp_Items.get(i).support=findsupport2(allpath, p);
			}
			
			
			exploringItem.Cresp_Items=(ArrayList<ExploringItem.Item>)exploringItem.CK_Items.clone();
			//remove  items that their support less than minsup 
			exploringItem.CK_Items.clear();
			for(int r=0;r<=exploringItem.Ctemp_Items.size()-1;r++){
				if(exploringItem.Ctemp_Items.get(r).support>=minsup){
					exploringItem.CK_Items.add(exploringItem.Ctemp_Items.get(r));
				}
			}
		}///end of for
		///////////////
		
		exploringItem.Exportedpattern="";
		int max=0;
		for(int i=1;i<=exploringItem.Cresp_Items.size()-1;i++){
			if(exploringItem.Cresp_Items.get(i).support>exploringItem.Cresp_Items.get(max).support)
				max=i;
		}
		if(max<=exploringItem.Cresp_Items.size()-1)
			exploringItem.Exportedpattern=exploringItem.Cresp_Items.get(max).rules;
		
		/////////////////////////////////
		
		s=exploringItem.Exportedpattern.split(",");
		
		for(int w=0;w<=s.length-1;w++){
			if(!exploringItem.ExportedpatternNorepeat.contains(s[w])){
				exploringItem.ExportedpatternNorepeat.add(s[w]);
			}
		}
		
		
			
		//reorder the items of exploringItem.ExportedpatternNorepeat
		Integer[] order=new Integer[exploringItem.ExportedpatternNorepeat.size()];
		String path=exploringItem.allpath_From_S0_To_Max.get(0);
		for(int i=0;i<=exploringItem.ExportedpatternNorepeat.size()-1;i++){
			String r=exploringItem.ExportedpatternNorepeat.get(i);
			int j=path.indexOf(r);
			order[i]=j;
		}
		
		////sort order

      	boolean swapped = true;
      	int p = 0;
      	Integer  tmpI;
      	String tmpS;
      	while (swapped){
      		swapped = false;
              p++;
              for (int i = 0; i < order.length - p; i++) {
              		if (order[i] > order[i+1]) {
                            tmpI=order[i];
                            order[i+1]=order[i];
                            order[i]=tmpI;
              			
              				tmpS = exploringItem.ExportedpatternNorepeat.get(i);
              				exploringItem.ExportedpatternNorepeat.set(i, exploringItem.ExportedpatternNorepeat.get(i+1));
              				exploringItem.ExportedpatternNorepeat.set(i+1,tmpS);
                            swapped = true;
                      }
                }
          }
		
		
		//
		/////////////////////////////
			
	}
    
    /////////////
    private double findsupport(ArrayList<String>  allpath,String p){
		int freq=0;
		int allfreq=allpath.size();
		for(int i=0;i<=allpath.size()-1;i++){
			String s=allpath.get(i);
			if(s.contains(p))
				freq++;
			
		}
		return (double)freq/allfreq;
		
	}
    private double findsupport2(ArrayList<String>  allpath,String p){
		int freq=0;
		String[] ap=p.split(",");
		for(int i=0;i<=allpath.size()-1;i++){
			String s=allpath.get(i);
			boolean flag=true;
			int j=0;
			int k=0;
			while(flag && j<=ap.length-1){
				k=s.indexOf(ap[j],k);
				if(k<0)
					flag=false;
				k+=ap[j].length()+1;
				j++;
			}
			if(flag)
				freq++;
		}
		return (double)freq/allpath.size();
	}
    
/////////////////////////////////////////
///////////////////////////////////////////
    
      private void findOtherState_Max_EQU(ExploringItem exploringItems){
      	GraphState oldstate=exploringItems.State_Max_EQU;
      	int oldindex=-1;
      	for(int i=0;i<=exploringItems.allEQU_Count.size()-1;i++)
      		if(exploringItems.allcurStates.get(i).equals(oldstate)){
      			oldindex=i;
      			break;
      		}
      	if(oldindex>=0 && oldindex+1<=exploringItems.allEQU_Count.size()-1){
      		for(int j=oldindex+1;j<=exploringItems.allEQU_Count.size()-1;j++)
      			if(exploringItems.Max_EQU==exploringItems.allEQU_Count.get(j)){
      				exploringItems.Max_EQU=exploringItems.allEQU_Count.get(j);
          			exploringItems.State_Max_EQU=exploringItems.allcurStates.get(j);
          			break;
      			}
      		if(exploringItems.State_Max_EQU.equals(oldstate)){
      			exploringItems.State_Max_EQU=null;
      			exploringItems.Max_EQU=0;
      		}
      			
      	}else{
      		exploringItems.State_Max_EQU=null;
      		exploringItems.Max_EQU=0;
      	}
  }
  private void dfs(GraphState curstate,String path,Integer fitness ,ExploringItem exploringItems,GrammarModel grammermodel,Set<? extends GraphState> nodeset){
  		//fitness is only used for DEADLOCK detection
	  
	  	if(exploringItems.allpath_From_S0_To_Max.size()>=exploringItems.maxNum_allPathFs0TMax)
	  		return;
	  
  		if(curstate.toString().equals("s0")){
  			exploringItems.allpath_From_S0_To_Max.add(path);
  			exploringItems.allpath_From_S0_To_Max_fitness.add(fitness);
  		}
  		else{
  			ArrayList<String> prevStates=find_ALL_prevStates(grammermodel, nodeset, curstate,exploringItems);
  			for(int i=0;i<=prevStates.size()-1;i+=2){
  				String prevstateS=prevStates.get(i);
  				GraphState prevstate=null;
  				String rulename=prevStates.get(i+1);
  				for(GraphState ns :nodeset){
  					if(ns.toString().equals(prevstateS)){
  						prevstate=ns;
  						break;
  					}
  						
  				}
  			  	if(exploringItems.allpath_From_S0_To_Max.size()>=exploringItems.maxNum_allPathFs0TMax)
  			  		return;

  			  	Boolean isPropertyQsatisfied=false;
  			  	if(exploringItems.CTLproperty.equals("liveByDeadlock")){
		  			for (MatchResult next : prevstate.getMatches()) {
		    				String curRulename=next.toString();
		    				if(curRulename.equals(exploringItems.targetRule)){
		    					isPropertyQsatisfied=true;
		    					break;
		    				}
		  			}	 
  			  	}
  			  	if(!isPropertyQsatisfied)
  			  		dfs(prevstate,rulename+","+path, findOutDegreeOfCurState(exploringItems, curstate) +fitness,exploringItems, grammermodel, nodeset);
  			  	
  				if(exploringItems.allpath_From_S0_To_Max.size()>=exploringItems.maxNum_allPathFs0TMax)
  			  		return;

  			}
  		}
  		
  	}

    private Integer findOutDegreeOfCurState(ExploringItem exploringItems, GraphState state){
    	Integer degree=0;
    	for(int i=0;i<=exploringItems.allcurStates.size()-1;i++)
    		if(exploringItems.allcurStates.get(i).equals(state))
    			return exploringItems.allcurStatesOutDegree.get(i);
    	
    	return degree;
    }
  	private  ArrayList<String>  find_ALL_prevStates(GrammarModel grammermodel,Set<? extends GraphState> nodeset,GraphState curState,ExploringItem exploringItems){
  		////s0,go_hungry,s1,get_left,....
  		ArrayList<String> prevStates=new ArrayList<String>();
  		
  		int curdepth=0,prevdepth=0;
  		
  		GraphState prevState=null;
  		Rule r=null;
  		try{
  			for(GraphState ns :nodeset){
  				Set<? extends GraphTransition> grtr=ns.getTransitions();
  				for(GraphTransition gt:grtr){
  					GraphState sourceState=gt.source();
  					GraphState targetState=gt.target();
  					if(targetState.equals(curState)){
  						prevState=sourceState;
  						RuleModel rulemodel=grammermodel.getRuleModel(QualName.name(gt.text(false)));
  					    r=rulemodel.toResource().getCondition().getRule();
  					    if(prevState.getNumber()<curState.getNumber() && !prevStates.contains(prevState.toString()) ){
  					    	prevStates.add(prevState.toString());
  					    	prevStates.add(r.getQualName().toString());
  					    	
  					    	//if(exploringItems.maxDepthOfSearch>=6){
  						    	//if(prevStates.size()==4)
  						    		//return prevStates;
  					    	//}
  						    //else 
  						    //if(prevStates.size()==6)
  						    	//return prevStates;
  					    	
  					    }
  					}
  						
  				}
  			}
  		}
  		catch (FormatException e) {
  	           System.err.println(e.getMessage());
  	    }
  		
  		return prevStates;
  	}
  

////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
  	///This method is called from heuristicLearnFBFdoNext 
  	public GraphState heuLearnDMdoNext(ExploringItem exploringItems) {

  		////////////////////////////////
  		///CTLproperty= deadlock || reachability ||safetyByReach || livenessByCycle || liveByDeadlock
  				
  		
  		
  		
  		Set<QualName> sname= exploringItems.grammermodel.getNames(ResourceKind.RULE);
  		
  			
    	//////////////////////////////////////////////////////////
    	/////////////////////////////////////////////////////////
    	if(exploringItems.isFirstStep  && (exploringItems.CTLproperty.equals("reachability") || exploringItems.CTLproperty.equals("deadlock") || exploringItems.CTLproperty.equals("safetyByReach") || exploringItems.CTLproperty.equals("liveByDeadlock"))){
        	
    		GraphState initialState=getNextState();
        	GraphState state = initialState;
        	transientStack.clear();
        	clearPool();

    		
    		
    		int Maxrepeat=40;
    		
    		int repeat=1;

    		ArrayList<GraphState> allHCurState=new ArrayList<GraphState>();
    		ArrayList<String> allHRule=new ArrayList<String>();
    		ArrayList<GraphState> allHNextState=new ArrayList<GraphState>();
    		
    		int depth=0;
    		
    		while(repeat<=Maxrepeat && exploringItems.heuristicResult==null){
	        	state = initialState;
	        	depth=0;
        		boolean ischanged=true;
        		while(ischanged && depth<=exploringItems.maxDepth){
        			if(state==null){
        				state=initialState;
        				depth=0;
        			}
        			ischanged=false;
        			for(int i=0 ;i<=exploringItems.ExportedpatternNorepeat.size()-1 && exploringItems.heuristicResult==null && state!=null ;i++){
            			String rulename=exploringItems.ExportedpatternNorepeat.get(i);
            			List<MatchResult> matches = state.getMatches();
            			exploringItems.Number_Explored_States++;
            			if(matches.size()==0 ){
            				ischanged=false;
            				break;
            			}
            			
            			Boolean isQsatisfied=false;
            			if(exploringItems.CTLproperty.equals("liveByDeadlock")){
	            			for (MatchResult next : matches) {
	        	  				String curRulename=next.toString();
	        	  				if(curRulename.equals(exploringItems.targetRule)){
	        	  					isQsatisfied=true;
	                				break;
	        	  				}
	        	  			}
            			}
            			
            			if(isQsatisfied==true)
            				break;
            			
            			depth++;
            			if(ISstateHasMCtarget_FBFS(exploringItems,state)){
            				exploringItems.heuristicResult="reachability";
            				exploringItems.First_Found_Dead_depth=depth;
          					exploringItems.lastStateInReachability=state;
            				ischanged=false;
            				break;
            			}else if(matches.size()==0){
            				int rep=1;
            				while(rep<=1000 &&  state.getMatches().size()==0){
        		        		ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
        		        		for(int u=0;u<=allHCurState.size()-1;u++)
        		        			if(allHCurState.get(u).toString().equals(state.toString())
        		        					&& allHRule.get(u).equals(rulename) )
        		        				allstatet.add(allHNextState.get(u));
        		        		     			
		        				int n=allstatet.size();
	    		    			Double d=Math.random()*n;
	    		    			int x=d.intValue();	
	    		    			GraphState statet;
	    		    			if(n>0)
	    		    				statet=allstatet.get(x);
	    		    			else
	    		    				statet=initialState;
        		        		state=statet;
        		        		rep++;
            				}
            				if(state.getMatches().size()==0)
            					state=null;
            				
            				if(state!=null)
            					ischanged=true;
            				else
            					ischanged=false;
            				break;
            			}
            			ArrayList<String> seloutRulename=new ArrayList<String>();
    					ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
            			
    					for (MatchResult next : matches) {
        					if(next.toString().equals(rulename)){
        						seloutRulename.add(rulename);
    							selNext.add(next);
        					}
            			}
    					if(seloutRulename.size()!=0 && selNext.size()!=0){
        		        	int n=seloutRulename.size();
    		    			Double d=Math.random()*n;
    		    			int x=d.intValue();
        		        	try {
								state.applyMatch(selNext.get(x));
							} catch (InterruptedException e) {
								//do nothing
								e.printStackTrace();
							}
        		        	setNextState();
            				GraphState statet=getNextState();
            				ischanged=true;
            				
            				
            				
            				if(statet!=null){
	            				allHCurState.add(state);
	            				allHRule.add(seloutRulename.get(x));
	            				allHNextState.add(statet);
	            				
            				}
            				
            				if(statet!=null && ISstateHasMCtarget_FBFS(exploringItems,statet)){
            					exploringItems.heuristicResult="reachability";
            					exploringItems.First_Found_Dead_depth=depth;
              					exploringItems.lastStateInReachability=statet;
                				ischanged=false;
                				break;
            				}
        		        	if(statet!=null ){
        		        		state=statet;
        		        	}
        		        	if(statet==null){
        		        		ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
        		        		for(int u=0;u<=allHCurState.size()-1;u++)
        		        			if(allHCurState.get(u).toString().equals(state.toString())
        		        					&& allHRule.get(u).equals(seloutRulename.get(x)) )
        		        				allstatet.add(allHNextState.get(u));
        		        		     			
		        				n=allstatet.size();
	    		    			d=Math.random()*n;
	    		    			x=d.intValue();
	    		    			if(n>0)
	    		    				statet=allstatet.get(x);
	    		    			else
	    		    				statet=null;
        		        		state=statet;
	        		       }
        		        }///end if
            		}//for
        		} //while
            	repeat++;
	    	}//while
    		
        	return null;
    	}////////end if
    	//////////////////////////////////////////////////////////////
		//////////exploringItems.isFirstStep=false////////////////////////////////////////////////
    	if(!exploringItems.isFirstStep && (exploringItems.CTLproperty.equals("reachability") || exploringItems.CTLproperty.equals("deadlock") || exploringItems.CTLproperty.equals("safetyByReach") || exploringItems.CTLproperty.equals("liveByDeadlock"))){

    		int maxLevelToExplore=exploringItems.maxDepth;;
    		int mlevel=1;
    		
    		GraphState initialState=getNextState();
        	GraphState state = initialState;
        	transientStack.clear();
        	clearPool();
    		
    		GraphState nextstate=null;
    		GraphState curstate=initialState;
    		
    		String preRuleName=null;
    		String nextRuleName=null;
    		
    		
    		
    		
    		while(curstate!=null && exploringItems.heuristicResult==null && mlevel<=maxLevelToExplore){
    			
    			
    			ArrayList<String> seloutRulename=new ArrayList<String>();
    			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
    			
    			preRuleName=nextRuleName;
    		
    			
    			List<MatchResult> matches = curstate.getMatches();
    			exploringItems.Number_Explored_States++;
    			if(matches.size()==0 ){
    				curstate=null;
    				break;
    			}
    			
    			Boolean isQsatisfied=false;
    			if(exploringItems.CTLproperty.equals("liveByDeadlock")){
        			for (MatchResult next : matches) {
    	  				String curRulename=next.toString();
    	  				if(curRulename.equals(exploringItems.targetRule)){
    	  					curstate=null;
    	  					isQsatisfied=true;
            				break;
    	  				}
    	  			}
    			}
    			
    			if(isQsatisfied)
    				break;
    			
    			if(ISstateHasMCtarget_FBFS(exploringItems,curstate)){
    				exploringItems.heuristicResult="reachability";
    				exploringItems.First_Found_Dead_depth=mlevel-1;
  					exploringItems.lastStateInReachability=curstate;
    				curstate=null;
					nextstate=null;
					break;
    			}
    			for (MatchResult next : matches) {
    				String outRulename=next.toString();
    				if(outRulename.equals(exploringItems.targetRule)){
    					exploringItems.heuristicResult="reachability";
    					exploringItems.First_Found_Dead_depth=mlevel-1;
      					exploringItems.lastStateInReachability=curstate;
    					curstate=null;
    					nextstate=null;
    					break;
    				}
    				
    				nextRuleName=outRulename;
    				if(Is_exists_pre_next_FBFS(exploringItems, preRuleName, nextRuleName)){
    					seloutRulename.add(outRulename);
    					selNext.add(next);
    				}
    			}
    			nextstate=null;
        		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
        			nextstate=null;
        			while(!seloutRulename.isEmpty() && nextstate==null){
        				int n=seloutRulename.size();
    	    			Double d=Math.random()*n;
    	    			int x=d.intValue();
    	    			clearPool();
    	    			try {
							curstate.applyMatch(selNext.get(x));
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}
    	    			setNextState();
    					nextstate=getNextState();
    					nextRuleName=seloutRulename.get(x);
    					seloutRulename.remove(x);
    					selNext.remove(x);
    				}
        			
        			mlevel++;
       			}
        		curstate=nextstate;
    		} //end of while
    		return null;
    	}////end if
      	//////////////////////////////////////////////////////////////
    	//////////////////////////////////////////////////////////
    	if(exploringItems.CTLproperty.equals("liveByCycle")){
    		
    		GraphState initialState=getNextState();
        	GraphState state = initialState;
        	transientStack.clear();
        	clearPool();

    		int Maxrepeat=40;
    		int repeat=1;

    		ArrayList<GraphState> allHCurState=new ArrayList<GraphState>();
    		ArrayList<String> allHRule=new ArrayList<String>();
    		ArrayList<GraphState> allHNextState=new ArrayList<GraphState>();
    		
    		
    		
    		while(repeat<=Maxrepeat && exploringItems.heuristicResult==null){
    			exploringItems.pathLeadCycle.clear();
    			ExploringItem.StateRule staterule=exploringItems.getNewStateRule();
    			staterule.rule=null;
    			staterule.state=initialState;
    			exploringItems.pathLeadCycle.add(staterule);
    			
    			
        		state = initialState;
        		
        		boolean isPropertyQsatisfied=false;
        		if(state==null)
    				state=initialState;
    			for(int i=0;i<=exploringItems.ExportedpatternNorepeat.size()-1 && exploringItems.heuristicResult==null && state!=null ;i++){
        			String rulename=exploringItems.ExportedpatternNorepeat.get(i);
        			List<MatchResult> matches = state.getMatches();
        			exploringItems.Number_Explored_States++;
        			
        			for (MatchResult next : matches) {
        		        if(next.toString().equals(exploringItems.targetRule)){
        		        	isPropertyQsatisfied=true;
        		        	break;
        		        }
        		    }
        			if(isPropertyQsatisfied)
        				break;
        			
	        		if(matches.size()==0){
	        				ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
			        		for(int u=0;u<=allHCurState.size()-1;u++)
			        			if(allHCurState.get(u).toString().equals(state.toString())
			        					&& allHRule.get(u).equals(rulename) )
			        				allstatet.add(allHNextState.get(u));
			        		     			
	        				int n=allstatet.size();
			    			int x=(int)Math.random()*n;
			    			GraphState statet;
			    			if(n>0)
			    				statet=allstatet.get(x);
			    			else
			    				statet=null;
			        		state=statet;
			        		if(state!=null && !exploringItems.Alltype.contains(rulename)){
			        			
			        			///////detect a cycle
			        			for(int j=0;j<=exploringItems.pathLeadCycle.size()-1 && exploringItems.pathLeadCycle.size()>=2 ;j++){
			        				ExploringItem.StateRule bstaterule=exploringItems.pathLeadCycle.get(j);
			        				if(bstaterule.state.equals(state)){
			        					exploringItems.heuristicResult="reachability";
			        					exploringItems.First_Found_Dead_depth=exploringItems.pathLeadCycle.size();
			        					exploringItems.lastStateInReachability=state;
			        		        	break;
			        				}
			        			}
			        			if(exploringItems.heuristicResult!=null && exploringItems.heuristicResult.equals("reachability"))
			        				break;
			        			///////////////
			        			
			        			staterule=exploringItems.getNewStateRule();
			        			try {
									staterule.rule=(Rule)exploringItems.simulator.getModel().getGrammar().getGraphResource(ResourceKind.RULE,QualName.name(rulename)).toResource();
								} catch (FormatException e) {
								}
			        			staterule.state=state;
			        			exploringItems.pathLeadCycle.add(staterule);
			        		}
	    		    }
    				if(state.getMatches().size()==0){
    					state=null;
    					break;
    				}
        			ArrayList<String> seloutRulename=new ArrayList<String>();
					ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
        			
					for (MatchResult next : matches) {
    					if(next.toString().equals(rulename)){
    						seloutRulename.add(rulename);
							selNext.add(next);
    					}
        			}
					if(seloutRulename.size()!=0 && selNext.size()!=0){
    		        	int n=seloutRulename.size();
		    			Double d=Math.random()*n;
		    			int x=d.intValue();
    		        	RuleTransition ruletransition=null;
						try {
							ruletransition = state.applyMatch(selNext.get(x));
						} catch (InterruptedException e1) {
							// do nothing
							e1.printStackTrace();
						}
    		        	setNextState();
        				GraphState statet=getNextState();
        				if(statet==null && ruletransition!=null){
        					statet=ruletransition.target();
        				}
        				
        				if(statet!=null){
            				allHCurState.add(state);
            				allHRule.add(seloutRulename.get(x));
            				allHNextState.add(statet);
            			}
        				
        				if(statet!=null && ISstateHasMCtarget_FBFS(exploringItems,statet)){
        					isPropertyQsatisfied=true;
        		        	break;
        				}
    		        	if(statet!=null ){
    		        		state=statet;
    		        	}
    		        	if(statet==null){
    		        		ArrayList<GraphState> allstatet=new ArrayList<GraphState>();
    		        		for(int u=0;u<=allHCurState.size()-1;u++)
    		        			if(allHCurState.get(u).toString().equals(state.toString())
    		        					&& allHRule.get(u).equals(seloutRulename.get(x)) )
    		        				allstatet.add(allHNextState.get(u));
    		        		     			
	        				n=allstatet.size();
    		    			d=Math.random()*n;
    		    			x=d.intValue();
    		    			if(n>0)
    		    				statet=allstatet.get(x);
    		    			else
    		    				statet=null;
    		        		state=statet;
        		       }
    		        	if(state!=null &&  !exploringItems.Alltype.contains(rulename)){
    		        		///////detect a cycle
		        			for(int j=0;j<=exploringItems.pathLeadCycle.size()-1 && exploringItems.pathLeadCycle.size()>=2 ;j++){
		        				ExploringItem.StateRule bstaterule=exploringItems.pathLeadCycle.get(j);
		        				if(bstaterule.state.equals(state)){
		        					exploringItems.heuristicResult="reachability";
		        					exploringItems.First_Found_Dead_depth=exploringItems.pathLeadCycle.size();
		        					exploringItems.lastStateInReachability=state;
		        		        	break;
		        				}
		        			}
		        			if(exploringItems.heuristicResult!=null)
		        				break;
		        			///////////////
		        			
		        			
    		        		staterule=exploringItems.getNewStateRule();
		        			try {
		        				staterule.rule=(Rule)exploringItems.grammermodel.getGraphResource(ResourceKind.RULE, QualName.name(rulename)).toResource();
							} catch (FormatException e) {
							}
		        			staterule.state=state;
		        			exploringItems.pathLeadCycle.add(staterule);
    		        	}
    		        }///end if
        		}//for
	        	repeat++;
	    	}//while

    	}
      	    	
    	//////////////////////////////////////////////////////////////
    	/////////////////////////////////////////////////////////////
    	return null;
    
    }

  	///////////////////////////////////////////////
  	//////////////////////////////////////////////
  	private boolean Is_exists_pre_next_FBFS(ExploringItem exploringItems ,String preRulename,String nextRulename){
    	//if(preRulename==null)
    		return true;
    	
    	//[settleBill, payBill, BillGood, selectGood, BillGood, selectGood, createBill, takeCart]
    	
    	
    	/*  I have to comment following!!!!  
    	String[] a=exploringItems.orig_allpath_From_S0_To_Max.get(0).split(",");
    	for(int k=0;k<=a.length-1;k++)
    		exploringItems.allRulesNames.add(a[k]);
    	
    	
    	
    	
    	int i=exploringItems.allRulesNames.size()-1;
    	while(i>=1){
    		if(exploringItems.allRulesNames.get(i).equals(preRulename) && exploringItems.allRulesNames.get(i-1).equals(nextRulename))
    			break;
    		i--;
    	}
    	if(i>=1)
    		return true;
    	else
    		return false;
    	
    	*/
    }
 
      
     private  boolean ISstateHasMCtarget_FBFS(ExploringItem exploringItems,GraphState state){
  		boolean isexists=false;
  		
  		ArrayList<QualName> Alltype=exploringItems.Alltype;
  		
  		List<MatchResult> matches=state.getMatches();
  		boolean flag=true;
  		if(exploringItems.CTLproperty.equals("deadlock") || exploringItems.CTLproperty.equals("liveByDeadlock") ){
  			for (MatchResult next : matches) {
  				if(!Alltype.contains(QualName.name(next.toString()))){
  		        	flag=false;
  		        	break;
  		        }
  		        
  		    }
  			isexists=flag;

  		}else{
  			for (MatchResult next : matches) {
  		        if(next.toString().equals(exploringItems.targetRule)){
  		        	isexists=true;
  		        	break;
  		        }
  		    }

  		}
  		
  		
  		
  		return isexists;
  	}

    
////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////GA///////////GA///////////////////////////////////////////////////////
////////////////////////GA///////////GA//////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

    public GraphState heuristicGAdoNext(ExploringGaBayesNet exploreGaBayesNet) {
    	
    	if(exploreGaBayesNet.WhatStep.equals("CIP")){   //createInitialPopulation
    		createInitialPopulation_GA(exploreGaBayesNet);
    		
    	}
    	if(exploreGaBayesNet.WhatStep.equals("CFN")){  //CalcFitness)  
    		calcfitness_of_Chr(exploreGaBayesNet);;  //Genetic Algoritm
    	}
    	
    	if(exploreGaBayesNet.RunningTime_AllFitnessFuncs==0)
    		exploreGaBayesNet.RunningTime_AllFitnessFuncs=0;
    	
    	return null; 
    }

    private void createInitialPopulation_GA(ExploringGaBayesNet exploreGaBayesNet){
    	int maxLevelToExplore=exploreGaBayesNet.DepthOfSearch;
    	int CountOFpopulation=exploreGaBayesNet.CountOFpopulation;
    	
    	int mlevel=1;
		
    	
		GraphState initialState=null;
    	if(!exploreGaBayesNet.callFromHeuGenerator)
    		initialState=exploreGaBayesNet.simulator.getModel().getGTS().startState();
    	else
    		initialState=exploreGaBayesNet.initialState;
    	
    	transientStack.clear();
    	clearPool();
		
    	
    	ExploringGaBayesNet.Chromosome chromosome=exploreGaBayesNet.getNewChromosome();
    	
		GraphState nextstate=null;
		GraphState curstate=initialState;
		exploreGaBayesNet.Call_Number_Fitness++;
		while(curstate!=null && heuristicResult==null && mlevel<=maxLevelToExplore){
			
			ArrayList<String> seloutRulename=new ArrayList<String>();
			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
			
			
			List<MatchResult> matches = curstate.getMatches();
			exploreGaBayesNet.Number_Explored_States++;
			if(matches.size()==0){
				if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){
					heuristicResult="reachability";
					exploreGaBayesNet.lastStateInReachability=curstate;
					exploreGaBayesNet.chroIndexCounterExamlpe=exploreGaBayesNet.population.size();
				}
				curstate=null;
				break;
			}else
			{
				if(ISstateHasMCtargetGA_matches(exploreGaBayesNet, matches, exploreGaBayesNet.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploreGaBayesNet.lastStateInReachability=curstate;
					exploreGaBayesNet.chroIndexCounterExamlpe=exploreGaBayesNet.population.size();
					curstate=null;
					break;
				}
					
			}
			
			
			
			if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock"))
				chromosome.fitness+=matches.size();
				
			
			
			
			for (MatchResult next : matches) {
				String outRulename=next.toString();
				if(outRulename.equals(exploreGaBayesNet.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploreGaBayesNet.lastStateInReachability=curstate;
					exploreGaBayesNet.chroIndexCounterExamlpe=exploreGaBayesNet.population.size();
					curstate=null;
					nextstate=null;
					break;
				}
				
				seloutRulename.add(outRulename);
				selNext.add(next);
			
			}
			nextstate=null;
    		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
    			nextstate=null;
    			int x=-1;
    			String outRulename="";
				while(!seloutRulename.isEmpty() && nextstate==null){
    				int n=seloutRulename.size();
	    			Double d=Math.random()*n;
	    			x=d.intValue();
	    			outRulename=seloutRulename.get(x);
	    			clearPool();
	    			try {
						curstate.applyMatch(selNext.get(x));
					} catch (InterruptedException e) {
						// do nothing
						e.printStackTrace();
					}
	    			setNextState();
					nextstate=getNextState();
					seloutRulename.remove(x);
					selNext.remove(x);
				}
    			if(nextstate!=null){
    				chromosome.genes.add(x);
    				chromosome.ruleNames.add(outRulename);
    				chromosome.states.add(nextstate);
    				chromosome.lastState=nextstate;    //each step, is updated!!!
    				if(exploreGaBayesNet.maxValueInAllChromosomes<x)
    					exploreGaBayesNet.maxValueInAllChromosomes=x;
    			}
    			else
    				break;
    			
    		}
    		mlevel++;
   			curstate=nextstate;
		} //end of while
		exploreGaBayesNet.heuristicResult=heuristicResult;
		exploreGaBayesNet.First_Found_Dead_depth=mlevel-1;
		
		if(!exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){  
			
			Set<? extends HostEdge> Host_edgeSet=null;
			if(heuristicResult!=null && heuristicResult.equals("reachability"))
				Host_edgeSet=exploreGaBayesNet.lastStateInReachability.getGraph().edgeSet();
			else
				Host_edgeSet=chromosome.lastState.getGraph().edgeSet();
      	  
         	
         	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
        	for(HostEdge he:Host_edgeSet)
        		HedgeList.add(he);  
        	
         	ArrayList<String> HnodeList=new ArrayList<String>();
         	for(HostEdge he:Host_edgeSet)
     			if(!HnodeList.contains(he.source().toString())){
     				HnodeList.add(he.source().toString());
     			}
         	
         	
         	long startTime = System.currentTimeMillis();
         	chromosome.fitness=findEQU_GA(exploreGaBayesNet,HedgeList,HnodeList);
         	long reportTime= System.currentTimeMillis() - startTime;
         	exploreGaBayesNet.RunningTime_AllFitnessFuncs+=reportTime;
         	
         	if(heuristicResult!=null && heuristicResult.equals("reachability"))
         		exploreGaBayesNet.OPTValueOfFitness=chromosome.fitness;
         	
		}

		
		exploreGaBayesNet.population.add(chromosome);
		exploreGaBayesNet.totalFitness+=chromosome.fitness;
		
    }
    
    private void calcfitness_of_Chr(ExploringGaBayesNet exploreGaBayesNet){
    	ExploringGaBayesNet.Chromosome chromosome=exploreGaBayesNet.population.get(exploreGaBayesNet.chroIndex);
    	chromosome.states.clear();
    	chromosome.fitness=0;
    	int gindex=0;  //gene index
    	int maxLevelToExplore=chromosome.genes.size();
    	
		
    	exploreGaBayesNet.chroIndexCounterExamlpe=exploreGaBayesNet.chroIndex;
    	
	
    	GraphState initialState=null;
		if(!exploreGaBayesNet.callFromHeuGenerator)
    		initialState=exploreGaBayesNet.simulator.getModel().getGTS().startState();
    	else
    		initialState=exploreGaBayesNet.initialState;
    	
    	transientStack.clear();
    	clearPool();
		GraphState nextstate=null;
		GraphState curstate=initialState;
		exploreGaBayesNet.Call_Number_Fitness++;
		while(curstate!=null && heuristicResult==null && gindex<maxLevelToExplore){
			
			ArrayList<String> seloutRulename=new ArrayList<String>();
			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
			
			
			List<MatchResult> matches = curstate.getMatches();
			exploreGaBayesNet.Number_Explored_States++;
			if(matches.size()==0){
				if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){
					heuristicResult="reachability";
					exploreGaBayesNet.lastStateInReachability=curstate;
				}
				curstate=null;
				break;
			}else
			{
				if(ISstateHasMCtargetGA_state(exploreGaBayesNet, curstate, exploreGaBayesNet.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploreGaBayesNet.lastStateInReachability=curstate;
					curstate=null;
					break;
				}
					
			}
			
			if(exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock"))
				chromosome.fitness+=matches.size();
			
			
			
			for (MatchResult next : matches) {
				String outRulename=next.toString();
				if(outRulename.equals(exploreGaBayesNet.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploreGaBayesNet.lastStateInReachability=curstate;
					curstate=null;
					nextstate=null;
					break;
				}
				
				seloutRulename.add(outRulename);
				selNext.add(next);
				
			}
			nextstate=null;
    		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
    			String outRulename="";
    			int x=-1;
    			int y=chromosome.genes.get(gindex);
    			if(y<seloutRulename.size()){
	    			outRulename=seloutRulename.get(y);
	    			clearPool();
	    			try {
						curstate.applyMatch(selNext.get(y));
					} catch (InterruptedException e) {
						// do nothing
						e.printStackTrace();
					}
	    			x=y;
	    			setNextState();
					nextstate=getNextState();
					if(curstate.equals(nextstate))
						nextstate=null;
					seloutRulename.remove(y);
					selNext.remove(y);
	    			outRulename="";
    			}
				while(!seloutRulename.isEmpty() && nextstate==null){
    				int n=seloutRulename.size();
	    			Double d=Math.random()*n;
	    			x=d.intValue();
	    			outRulename=seloutRulename.get(x);
	    			clearPool();
	    			try {
						curstate.applyMatch(selNext.get(x));
					} catch (InterruptedException e) {
						// do nothing
						e.printStackTrace();
					}
	    			setNextState();
					nextstate=getNextState();
					if(curstate.equals(nextstate))
						nextstate=null;
					seloutRulename.remove(x);
					selNext.remove(x);
				}
				if(x>=0)
					chromosome.genes.set(gindex, x);
				if(nextstate==null)
    				break;
    			else{
    				chromosome.lastState=nextstate;    //each step, is updated!!!
    				chromosome.states.add(nextstate);
    			}
    		} //end if
    		gindex++;
   			curstate=nextstate;
		} //end of while
		exploreGaBayesNet.heuristicResult=heuristicResult;
		exploreGaBayesNet.First_Found_Dead_depth=gindex;
		
		if(!exploreGaBayesNet.ModelCheckingTarget.equals("DeadLock")){  
	
        	Set<? extends HostEdge> Host_edgeSet=null;
			if(heuristicResult!=null && heuristicResult.equals("reachability"))
				Host_edgeSet=exploreGaBayesNet.lastStateInReachability.getGraph().edgeSet();
			else
				Host_edgeSet=chromosome.lastState.getGraph().edgeSet();


        	
         	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
        	for(HostEdge he:Host_edgeSet)
        		HedgeList.add(he);  
        	
         	ArrayList<String> HnodeList=new ArrayList<String>();
         	for(HostEdge he:Host_edgeSet)
     			if(!HnodeList.contains(he.source().toString())){
     				HnodeList.add(he.source().toString());
     			}
         	
         	long startTime = System.currentTimeMillis();
         	chromosome.fitness=findEQU_GA(exploreGaBayesNet,HedgeList,HnodeList);
         	long reportTime= System.currentTimeMillis() - startTime;
         	exploreGaBayesNet.RunningTime_AllFitnessFuncs+=reportTime;
         	if(heuristicResult!=null && heuristicResult.equals("reachability"))
         		exploreGaBayesNet.OPTValueOfFitness=chromosome.fitness;
         	
		}
		
		exploreGaBayesNet.population.set(exploreGaBayesNet.chroIndex,chromosome);
		exploreGaBayesNet.totalFitness+=chromosome.fitness;
	
		
    }
    private  boolean ISstateHasMCtargetGA_state(ExploringGaBayesNet exploreGaBayesNet,GraphState curstate,String ModelCheckingTarget ){
		boolean isexists=false;
		
		ArrayList<QualName> Alltype=exploreGaBayesNet.Alltype;
		List<MatchResult> matches=curstate.getMatches();
		boolean flag=true;
		if(ModelCheckingTarget.equals("DeadLock")){
			for (MatchResult next : matches) {
		        if(!Alltype.contains(QualName.name(next.toString()))){
		        	flag=false;
		        	break;
		        }
		        
		    }
			isexists=flag;

		}else{
			for (MatchResult next : matches) {
		        if(next.toString().equals(ModelCheckingTarget)){
		        	isexists=true;
		        	break;
		        }
		    }

		}
			
		return isexists;
	}
    
    private  boolean ISstateHasMCtargetGA_matches(ExploringGaBayesNet exploreGaBayesNet,List<MatchResult> matches,String ModelCheckingTarget ){
		boolean isexists=false;
		
		ArrayList<QualName> Alltype=exploreGaBayesNet.Alltype;
		
		boolean flag=true;
		if(ModelCheckingTarget.equals("DeadLock")){
			for (MatchResult next : matches) {
				if(!Alltype.contains(QualName.name(next.toString()))){
		        	flag=false;
		        	break;
		        }
		        
		    }
			isexists=flag;

		}else{
			for (MatchResult next : matches) {
		        if(next.toString().equals(ModelCheckingTarget)){
		        	isexists=true;
		        	break;
		        }
		    }

		}
			
		return isexists;
	}
    
	private int findEQU_GA(ExploringGaBayesNet exploreGaBayesNet,ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList){
		
		ArrayList<RuleEdge> TedgeList=exploreGaBayesNet.targetGraph_edgeList;
    	ArrayList<RuleNode> TnodeList=exploreGaBayesNet.targetGraph_nodeList;
    	///////////////////////////////////////////////////////////////
    	/////////////////////////////find positive equality////////////
    	//////////////////////////////////////////////////////////////
    	exploreGaBayesNet.allinfo.clear();
    	for(int i=0;i<=TnodeList.size()-1;i++)    
    		for(int j=0;j<=HnodeList.size()-1;j++) {   
	    		Exploringinfo  einfo=new Exploringinfo();
    			einfo.tnode=TnodeList.get(i).toString();
    			einfo.hnode=HnodeList.get(j).toString();
    			exploreGaBayesNet.allinfo.add(einfo);
	        }
	      
    	for(int i=0;i<=exploreGaBayesNet.allinfo.size()-1;i++){
    		Exploringinfo  einfo=exploreGaBayesNet.allinfo.get(i);
    		String tn=einfo.tnode;
    		String hn=einfo.hnode;
    		int equall_count=0;
    		int tnode_edges_count=0;
    		
    		ArrayList<String> hedges=new ArrayList<String>();
    		
    		for(int k=0;k<=TedgeList.size()-1;k++){
    			RuleEdge ae=TedgeList.get(k);
    			if(ae.source().toString().equals(tn)){
    				tnode_edges_count++;
    				String tlabel=ae.label().toString();
    				for(int p=0;p<=HedgeList.size()-1;p++){
    					HostEdge he=HedgeList.get(p);
    					if(he.source().toString().equals(hn) && he.label().toString().equals(tlabel) && !hedges.contains(he.toString()))
    					{equall_count++;hedges.add(he.toString());break;}
    				}
    			}
    		}
    		einfo.equall_count=equall_count;
    		einfo.tnode_edges_count=tnode_edges_count;
    		einfo.diff=tnode_edges_count-equall_count;
    		if(einfo.diff==0 && i<exploreGaBayesNet.allinfo.size()-1){
    			int j=i+1;
    			Exploringinfo  einfoo=exploreGaBayesNet.allinfo.get(j);
    			while(j<=exploreGaBayesNet.allinfo.size()-1){
    				if((einfoo.hnode.equals(hn) || einfoo.tnode.equals(tn) )){
    					exploreGaBayesNet.allinfo.remove(j);
    					j=j;
    				}else
    					j++;
    				if(j<=exploreGaBayesNet.allinfo.size()-1)
    					einfoo=exploreGaBayesNet.allinfo.get(j);
    			}
    		}
    	}
    	
    	///////////////////////////////bubble sort///
    	///sort based on equall_count Descending (from greater to smaller)
    	
    	boolean swapped = true;
    	int p = 0;
    	Exploringinfo  tmp;
    	while (swapped){
    		swapped = false;
            p++;
            for (int i = 0; i < exploreGaBayesNet.allinfo.size() - p; i++) {
            		if (exploreGaBayesNet.allinfo.get(i).equall_count < exploreGaBayesNet.allinfo.get(i+1).equall_count) {
                          tmp = exploreGaBayesNet.allinfo.get(i);
                          exploreGaBayesNet.allinfo.set(i, exploreGaBayesNet.allinfo.get(i+1));
                          exploreGaBayesNet.allinfo.set(i+1,tmp);
                          swapped = true;
                    }
              }
        }
    	//////////////////////////////
    	ArrayList<String> tnodes=new ArrayList<String>();
    	ArrayList<String> hnodes=new ArrayList<String>();
    	int EQU_Count=0;
    	for(int i=0;i<=exploreGaBayesNet.allinfo.size()-1;i++){
    		Exploringinfo  einfo=exploreGaBayesNet.allinfo.get(i);
    		String tn=einfo.tnode;
    		String hn=einfo.hnode;
    		if(!tnodes.contains(tn) && !hnodes.contains(hn)){
    			tnodes.add(tn);
    			hnodes.add(hn);
    			EQU_Count+=einfo.equall_count;
    		}
    	}
    		
    	
    	///////////////////////////////////////////////////////////////
    	/////////////////////////////find negative equality////////////
    	///////////////////////////////////////////////////////////////
    	if(exploreGaBayesNet.allNACs==null)
    		return EQU_Count;
    	int NegEQU_Count=0;
    	@SuppressWarnings("unchecked")
		ArrayList<groove.verify.ExploringGaBayesNet.NAC> allNACs= (ArrayList<groove.verify.ExploringGaBayesNet.NAC>) exploreGaBayesNet.allNACs.clone();
    	for(int i=0;i<=exploreGaBayesNet.allNACs.size()-1;i++){
    		searchNacEquallNodes_GA(HedgeList, HnodeList, exploreGaBayesNet, i);
    		ExploringGaBayesNet.NAC nac=allNACs.get(i);
    		if(nac.ANacEqualNodes.size()==0)
    			continue;
    		ArrayList<RuleNode> tnodeList=new ArrayList<RuleNode>();
    		for(int j=0;j<=nac.ruleedgeList.size()-1;j++){
    			RuleEdge tEdge=nac.ruleedgeList.get(j);
    			RuleNode tNode=tEdge.source();
    			if(tEdge.isLoop() && isSingleNode_GA(nac,tNode) && !tnodeList.contains(tNode)){
    				int tIndex=IndexOfNodeInANac_GA(nac, tNode);
    				NegEQU_Count+=nac.ANacEqualNodes.get(tIndex).HEList.size();
    				tnodeList.add(tNode);
    			}else if(!tEdge.isLoop()){
    				RuleNode tNodeSource=tEdge.source();
    				RuleNode tNodeTarget=tEdge.target();
    				tnodeList.add(tNodeSource);
    				if(tNodeTarget.toString().contains("bool")){
    					int tSourceIndex=IndexOfNodeInANac_GA(nac, tNodeSource);
	    				NegEQU_Count+=nac.ANacEqualNodes.get(tSourceIndex).HEList.size();
    				}else{
	    				tnodeList.add(tNodeTarget);
	    				int tSourceIndex=IndexOfNodeInANac_GA(nac, tNodeSource);
	    				if(tSourceIndex==-1)
	    					continue;
	    				int tTargetIndex=IndexOfNodeInANac_GA(nac, tNodeTarget);
	    				if(tTargetIndex==-1)
	    					continue;
	    				ExploringGaBayesNet.NacEqualNode tSourceEqualNode=nac.ANacEqualNodes.get(tSourceIndex);
	    				ExploringGaBayesNet.NacEqualNode tTargetEqualNode=nac.ANacEqualNodes.get(tTargetIndex);
	    				for(int k=0;k<=tSourceEqualNode.HEList.size()-1;k++){
	    					String hNodeSource=tSourceEqualNode.HEList.get(k);
	    					for(int q=0;q<=tTargetEqualNode.HEList.size()-1;q++){
	    						String hNodeTarget=tTargetEqualNode.HEList.get(q);
	    						if(isExistsEdgeWithLabel_GA(HedgeList,hNodeSource, hNodeTarget, tEdge.label().toString())){
	    							NegEQU_Count++;
	    						}
	    					}
	    				}
    				}
    			}
    		}
    		
    	
    	}
       	////////////////////////////////////////////////
     	return EQU_Count-NegEQU_Count;
    }
	private boolean isExistsEdgeWithLabel_GA(ArrayList<HostEdge>  HedgeList,String hNodeSource,String hNodeTarget,String label){
    	for(int i=0;i<=HedgeList.size()-1;i++){
    		HostEdge hEdge=HedgeList.get(i);
    		if(hEdge.source().toString().equals(hNodeSource) && hEdge.target().toString().equals(hNodeTarget) && hEdge.label().toString().equals(label))
    			return true;
    	}
    	return false;
    }
    private void searchNacEquallNodes_GA(ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList,ExploringGaBayesNet exploreGaBayesNet,int NacIndex){
    	ExploringGaBayesNet.NAC nac=exploreGaBayesNet.allNACs.get(NacIndex);
    	nac.ANacEqualNodes.clear();
    	for(int i=0;i<=nac.rulenodeList.size()-1;i++){
    		ExploringGaBayesNet.NacEqualNode nacEqualNode=null;
    		RuleNode tNode=nac.rulenodeList.get(i);
    		if(tNode.toString().contains("bool"))
    			continue;
    		for(int j=0;j<=HnodeList.size()-1;j++){
    			String hNode=HnodeList.get(j);
    			boolean isContinue=true;
    			for(int k=0;k<=nac.ruleedgeList.size()-1 && isContinue;k++){
        			RuleEdge tEdge=nac.ruleedgeList.get(k);
        			if(tEdge.isLoop() && tEdge.source().equals(tNode)){
        				boolean isFind=false;
        				for(int p=0;p<=HedgeList.size()-1;p++){
        					HostEdge hEdge=HedgeList.get(p);
        					if(hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode)){
        						isFind=true;
        						break;
        					}
        				}
        				isContinue=isFind;
        			}else if(!tEdge.isLoop() && tEdge.source().equals(tNode) && tEdge.target().toString().contains("bool")){
        				boolean isFind=false;
        				for(int p=0;p<=HedgeList.size()-1;p++){
        					HostEdge hEdge=HedgeList.get(p);
        					if(!hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode) && hEdge.target().toString().contains(tEdge.target().toString())){
        						isFind=true;
        						break;
        					}
        				}
        				isContinue=isFind;
        			}
    			}
    			if(isContinue){
    				if(nacEqualNode==null)
    					nacEqualNode=exploreGaBayesNet.getNewNacEqualNode();
    				nacEqualNode.tNode=tNode;
    				nacEqualNode.HEList.add(hNode);
    			}
    		}
    		if(nacEqualNode!=null)
    			nac.ANacEqualNodes.add(nacEqualNode);
    	}
    	exploreGaBayesNet.allNACs.set(NacIndex,nac);    	
    }
    private boolean isSingleNode_GA(ExploringGaBayesNet.NAC nac,RuleNode tNode){
    	boolean isSingle=true;
    	for(int q=0;q<=nac.ruleedgeList.size()-1;q++){
			RuleEdge tEdge=nac.ruleedgeList.get(q);
			if(!tEdge.isLoop() && (tEdge.source().equals(tNode) || tEdge.target().equals(tNode))){
				isSingle=false;
				break;
			}
		}
    	return isSingle;
    }
 
    private int IndexOfNodeInANac_GA(ExploringGaBayesNet.NAC nac,RuleNode tNode){
      	for(int i=0;i<=nac.ANacEqualNodes.size()-1;i++)
    		if(nac.ANacEqualNodes.get(i).tNode.equals(tNode)){
    			return i;
    		}
    	return -1;
    }

////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////PSO//////////////////////////////////////////////////////////////////////
//////////////////////PSO//////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

public GraphState heuristicPSOdoNext(ExploringItemPSO exploringItemPSO) {
    	
    	if(exploringItemPSO.WhatStep.equals("CIP")){   //createInitialPopulation
    		createInitialPopulation_PSO(exploringItemPSO);
    	}
    	if(exploringItemPSO.WhatStep.equals("CFN")){  //CalcFitness)  
    		calcfitness_of_Particle(exploringItemPSO);  
    	}
    	
    	return null;
    }
    
	private void createInitialPopulation_PSO(ExploringItemPSO exploringItemPSO){
		int maxLevelToExplore=exploringItemPSO.DepthOfSearch;
		int CountOFpopulation=exploringItemPSO.CountOFpopulation;
		
		int mlevel=1;
		
		
		GraphState initialState=null;
		if(!exploringItemPSO.callFromHeuGenerator)
			initialState=exploringItemPSO.simulator.getModel().getGTS().startState();
		else
			initialState=exploringItemPSO.initialState;
		
		transientStack.clear();
		clearPool();
		
		
		ExploringItemPSO.Particle particle=exploringItemPSO.getNewParticle();
		
		GraphState nextstate=null;
		GraphState curstate=initialState;
		exploringItemPSO.Call_Number_Fitness++;
		while(curstate!=null && heuristicResult==null && mlevel<=maxLevelToExplore){
			
			ArrayList<String> seloutRulename=new ArrayList<String>();
			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
			
			
			List<MatchResult> matches = curstate.getMatches();
			exploringItemPSO.Number_Explored_States++;
			if(matches.size()==0){
				if(exploringItemPSO.ModelCheckingTarget.equals("DeadLock")){
					heuristicResult="reachability";
					exploringItemPSO.lastStateInReachability=curstate;
					exploringItemPSO.partIndexCounterExamlpe=exploringItemPSO.population.size();
				}
				curstate=null;
				break;
			}else
			{
				if(ISstateHasMCtargetPSO_matches(exploringItemPSO, matches, exploringItemPSO.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploringItemPSO.lastStateInReachability=curstate;
					exploringItemPSO.partIndexCounterExamlpe=exploringItemPSO.population.size();
					curstate=null;
					break;
				}
					
			}
			
			
			
			if(exploringItemPSO.ModelCheckingTarget.equals("DeadLock"))
				particle.fitness+=matches.size();
				
			
			
			
			for (MatchResult next : matches) {
				String outRulename=next.toString();
				if(outRulename.equals(exploringItemPSO.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploringItemPSO.lastStateInReachability=curstate;
					exploringItemPSO.partIndexCounterExamlpe=exploringItemPSO.population.size();
					curstate=null;
					nextstate=null;
					break;
				}
				
				seloutRulename.add(outRulename);
				selNext.add(next);
			
			}
			nextstate=null;
			if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
				nextstate=null;
				int x=-1;
				String outRulename="";
				while(!seloutRulename.isEmpty() && nextstate==null){
					int n=seloutRulename.size();
	    			Double d=Math.random()*n;
	    			x=d.intValue();
	    			outRulename=seloutRulename.get(x);
	    			clearPool();
	    			try {
						curstate.applyMatch(selNext.get(x));
					} catch (InterruptedException e) {
						// do nothing
						e.printStackTrace();
					}
	    			setNextState();
					nextstate=getNextState();
					seloutRulename.remove(x);
					selNext.remove(x);
				}
				if(nextstate!=null){
					particle.genes.add(x);
					particle.ruleNames.add(outRulename);
					particle.states.add(nextstate);
					particle.lastState=nextstate;    //each step, is updated!!!
					if(exploringItemPSO.maxValueInAllParticles<x)
						exploringItemPSO.maxValueInAllParticles=x;
				}
				else
					break;
				
			}
			mlevel++;
			curstate=nextstate;
		} //end of while
		exploringItemPSO.heuristicResult=heuristicResult;
		exploringItemPSO.First_Found_Dead_depth=mlevel-1;
		
		if(!exploringItemPSO.ModelCheckingTarget.equals("DeadLock")){  
		
	    	
	    	//////////////
	    	Set<? extends HostEdge> Host_edgeSet=particle.lastState.getGraph().edgeSet();
	  	  
	     	
	     	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
	    	for(HostEdge he:Host_edgeSet)
	    		HedgeList.add(he);  
	    	
	     	ArrayList<String> HnodeList=new ArrayList<String>();
	     	for(HostEdge he:Host_edgeSet)
	 			if(!HnodeList.contains(he.source().toString())){
	 				HnodeList.add(he.source().toString());
	 			}
	     	
	    	particle.fitness=findEQU_PSO(exploringItemPSO,HedgeList,HnodeList);
		}
	
		
		exploringItemPSO.population.add(particle);
		exploringItemPSO.totalFitness+=particle.fitness;
	}
    private void calcfitness_of_Particle(ExploringItemPSO exploringItemPSO){
    	ExploringItemPSO.Particle particle=exploringItemPSO.population.get(exploringItemPSO.partIndex);
    	particle.states.clear();
    	particle.fitness=0;
    	int gindex=0;  //gene index
    	int maxLevelToExplore=particle.genes.size();
    	
		
    	exploringItemPSO.partIndexCounterExamlpe=exploringItemPSO.partIndex;
    	
	
    	GraphState initialState=null;
		if(!exploringItemPSO.callFromHeuGenerator)
    		initialState=exploringItemPSO.simulator.getModel().getGTS().startState();
    	else
    		initialState=exploringItemPSO.initialState;
    	
    	transientStack.clear();
    	clearPool();
		GraphState nextstate=null;
		GraphState curstate=initialState;
		exploringItemPSO.Call_Number_Fitness++;
		while(curstate!=null && heuristicResult==null && gindex<maxLevelToExplore){
			
			ArrayList<String> seloutRulename=new ArrayList<String>();
			ArrayList<MatchResult> selNext=new ArrayList<MatchResult>();
			
			
			List<MatchResult> matches = curstate.getMatches();
			exploringItemPSO.Number_Explored_States++;
			if(matches.size()==0){
				if(exploringItemPSO.ModelCheckingTarget.equals("DeadLock")){
					heuristicResult="reachability";
					exploringItemPSO.lastStateInReachability=curstate;
				}
				curstate=null;
				break;
			}else
			{
				if(ISstateHasMCtargetPSO_state(exploringItemPSO, curstate, exploringItemPSO.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploringItemPSO.lastStateInReachability=curstate;
					curstate=null;
					break;
				}
					
			}
			
			if(exploringItemPSO.ModelCheckingTarget.equals("DeadLock"))
				particle.fitness+=matches.size();
			
			
			
			for (MatchResult next : matches) {
				String outRulename=next.toString();
				if(outRulename.equals(exploringItemPSO.ModelCheckingTarget)){
					heuristicResult="reachability";
					exploringItemPSO.lastStateInReachability=curstate;
					curstate=null;
					nextstate=null;
					break;
				}
				
				seloutRulename.add(outRulename);
				selNext.add(next);
				
			}
			nextstate=null;
    		if(seloutRulename.size()!=0 && selNext.size()!=0 && curstate!=null){
    			String outRulename="";
    			int x=-1;
    			int y=-1;
    			if(gindex<particle.genes.size())
    				y=particle.genes.get(gindex);
    			if(y>=0 && y<seloutRulename.size()){
	    			outRulename=seloutRulename.get(y);
	    			clearPool();
	    			try {
						curstate.applyMatch(selNext.get(y));
					} catch (InterruptedException e) {
						// do nothing
						e.printStackTrace();
					}
	    			x=y;
	    			setNextState();
					nextstate=getNextState();
					if(curstate.equals(nextstate))
						nextstate=null;
					seloutRulename.remove(y);
					selNext.remove(y);
	    			outRulename="";
    			}
				while(!seloutRulename.isEmpty() && nextstate==null){
    				int n=seloutRulename.size();
	    			Double d=Math.random()*n;
	    			x=d.intValue();
	    			outRulename=seloutRulename.get(x);
	    			clearPool();
	    			try {
						curstate.applyMatch(selNext.get(x));
					} catch (InterruptedException e) {
						// do nothing
						e.printStackTrace();
					}
	    			setNextState();
					nextstate=getNextState();
					if(curstate.equals(nextstate))
						nextstate=null;
					seloutRulename.remove(x);
					selNext.remove(x);
				}
				if(x>=0 && gindex<particle.genes.size())
					particle.genes.set(gindex, x);
				
				
				if(nextstate==null)
    				break;
    			else{
    				particle.lastState=nextstate;    //each step, is updated!!!
    				particle.states.add(nextstate);
    			}
    		} //end if
    		gindex++;
   			curstate=nextstate;
		} //end of while
		exploringItemPSO.heuristicResult=heuristicResult;
		exploringItemPSO.First_Found_Dead_depth=gindex;
		
		if(!exploringItemPSO.ModelCheckingTarget.equals("DeadLock") && exploringItemPSO.heuristicResult==null){  
	
        	
        	//////////////
        	Set<? extends HostEdge> Host_edgeSet=particle.lastState.getGraph().edgeSet();
      	  
        	
         	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
        	for(HostEdge he:Host_edgeSet)
        		HedgeList.add(he);  
        	
         	ArrayList<String> HnodeList=new ArrayList<String>();
         	for(HostEdge he:Host_edgeSet)
     			if(!HnodeList.contains(he.source().toString())){
     				HnodeList.add(he.source().toString());
     			}
         	
         	particle.fitness=findEQU_PSO(exploringItemPSO,HedgeList,HnodeList);
		}
		
		exploringItemPSO.population.set(exploringItemPSO.partIndex,particle);
		exploringItemPSO.totalFitness+=particle.fitness;
	
    }
    
    private  boolean ISstateHasMCtargetPSO_matches(ExploringItemPSO exploringItemPSO,List<MatchResult> matches,String ModelCheckingTarget ){
		boolean isexists=false;
		
		ArrayList<QualName> Alltype=exploringItemPSO.Alltype;
		
		boolean flag=true;
		if(ModelCheckingTarget.equals("DeadLock")){
			for (MatchResult next : matches) {
		        if(!Alltype.contains(QualName.name(next.toString()))){
		        	flag=false;
		        	break;
		        }
		        
		    }
			isexists=flag;

		}else{
			for (MatchResult next : matches) {
		        if(next.toString().equals(ModelCheckingTarget)){
		        	isexists=true;
		        	break;
		        }
		    }

		}
			
		return isexists;
	}
    @SuppressWarnings("unlikely-arg-type")
	private  boolean ISstateHasMCtargetPSO_state(ExploringItemPSO exploringItemPSO,GraphState curstate,String ModelCheckingTarget ){
		boolean isexists=false;
		
		ArrayList<QualName> Alltype=exploringItemPSO.Alltype;
		List<MatchResult> matches=curstate.getMatches();
		boolean flag=true;
		if(ModelCheckingTarget.equals("DeadLock")){
			for (MatchResult next : matches) {
		        if(!Alltype.contains(QualName.name(next.toString()))){
		        	flag=false;
		        	break;
		        }
		        
		    }
			isexists=flag;

		}else{
			for (MatchResult next : matches) {
		        if(next.toString().equals(ModelCheckingTarget)){
		        	isexists=true;
		        	break;
		        }
		    }

		}
			
		return isexists;
	}
    
	private int findEQU_PSO(ExploringItemPSO exploringItemPSO,ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList){
		
		ArrayList<RuleEdge> TedgeList=exploringItemPSO.targetGraph_edgeList;
    	ArrayList<RuleNode> TnodeList=exploringItemPSO.targetGraph_nodeList;
    	///////////////////////////////////////////////////////////////
    	/////////////////////////////find positive equality////////////
    	//////////////////////////////////////////////////////////////
    	exploringItemPSO.allinfo.clear();
    	for(int i=0;i<=TnodeList.size()-1;i++)    
    		for(int j=0;j<=HnodeList.size()-1;j++) {   
	    		Exploringinfo  einfo=new Exploringinfo();
    			einfo.tnode=TnodeList.get(i).toString();
    			einfo.hnode=HnodeList.get(j).toString();
    			exploringItemPSO.allinfo.add(einfo);
	        }
	      
    	for(int i=0;i<=exploringItemPSO.allinfo.size()-1;i++){
    		Exploringinfo  einfo=exploringItemPSO.allinfo.get(i);
    		String tn=einfo.tnode;
    		String hn=einfo.hnode;
    		int equall_count=0;
    		int tnode_edges_count=0;
    		
    		ArrayList<String> hedges=new ArrayList<String>();
    		
    		for(int k=0;k<=TedgeList.size()-1;k++){
    			RuleEdge ae=TedgeList.get(k);
    			if(ae.source().toString().equals(tn)){
    				tnode_edges_count++;
    				String tlabel=ae.label().toString();
    				for(int p=0;p<=HedgeList.size()-1;p++){
    					HostEdge he=HedgeList.get(p);
    					if(he.source().toString().equals(hn) && he.label().toString().equals(tlabel) && !hedges.contains(he.toString()))
    					{equall_count++;hedges.add(he.toString());break;}
    				}
    			}
    		}
    		einfo.equall_count=equall_count;
    		einfo.tnode_edges_count=tnode_edges_count;
    		einfo.diff=tnode_edges_count-equall_count;
    		if(einfo.diff==0 && i<exploringItemPSO.allinfo.size()-1){
    			int j=i+1;
    			Exploringinfo  einfoo=exploringItemPSO.allinfo.get(j);
    			while(j<=exploringItemPSO.allinfo.size()-1){
    				if((einfoo.hnode.equals(hn) || einfoo.tnode.equals(tn) )){
    					exploringItemPSO.allinfo.remove(j);
    					j=j;
    				}else
    					j++;
    				if(j<=exploringItemPSO.allinfo.size()-1)
    					einfoo=exploringItemPSO.allinfo.get(j);
    			}
    		}
    	}
    	
    	///////////////////////////////bubble sort///
    	///sort based on equall_count Descending (from greater to smaller)
    	
    	boolean swapped = true;
    	int p = 0;
    	Exploringinfo  tmp;
    	while (swapped){
    		swapped = false;
            p++;
            for (int i = 0; i < exploringItemPSO.allinfo.size() - p; i++) {
            		if (exploringItemPSO.allinfo.get(i).equall_count < exploringItemPSO.allinfo.get(i+1).equall_count) {
                          tmp = exploringItemPSO.allinfo.get(i);
                          exploringItemPSO.allinfo.set(i, exploringItemPSO.allinfo.get(i+1));
                          exploringItemPSO.allinfo.set(i+1,tmp);
                          swapped = true;
                    }
              }
        }
    	//////////////////////////////
    	ArrayList<String> tnodes=new ArrayList<String>();
    	ArrayList<String> hnodes=new ArrayList<String>();
    	int EQU_Count=0;
    	for(int i=0;i<=exploringItemPSO.allinfo.size()-1;i++){
    		Exploringinfo  einfo=exploringItemPSO.allinfo.get(i);
    		String tn=einfo.tnode;
    		String hn=einfo.hnode;
    		if(!tnodes.contains(tn) && !hnodes.contains(hn)){
    			tnodes.add(tn);
    			hnodes.add(hn);
    			EQU_Count+=einfo.equall_count;
    		}
    	}
    		
    	
    	///////////////////////////////////////////////////////////////
    	/////////////////////////////find negative equality////////////
    	///////////////////////////////////////////////////////////////
    	if(exploringItemPSO.allNACs==null)
    		return EQU_Count;
    	int NegEQU_Count=0;
    	@SuppressWarnings("unchecked")
		ArrayList<groove.verify.ExploringItemPSO.NAC> allNACs= (ArrayList<groove.verify.ExploringItemPSO.NAC>) exploringItemPSO.allNACs.clone();
    	for(int i=0;i<=exploringItemPSO.allNACs.size()-1;i++){
    		searchNacEquallNodes_PSO(HedgeList, HnodeList, exploringItemPSO, i);
    		ExploringItemPSO.NAC nac=allNACs.get(i);
    		if(nac.ANacEqualNodes.size()==0)
    			continue;
    		ArrayList<RuleNode> tnodeList=new ArrayList<RuleNode>();
    		for(int j=0;j<=nac.ruleedgeList.size()-1;j++){
    			RuleEdge tEdge=nac.ruleedgeList.get(j);
    			RuleNode tNode=tEdge.source();
    			if(tEdge.isLoop() && isSingleNode_PSO(nac,tNode) && !tnodeList.contains(tNode)){
    				int tIndex=IndexOfNodeInANac_PSO(nac, tNode);
    				NegEQU_Count+=nac.ANacEqualNodes.get(tIndex).HEList.size();
    				tnodeList.add(tNode);
    			}else if(!tEdge.isLoop()){
    				RuleNode tNodeSource=tEdge.source();
    				RuleNode tNodeTarget=tEdge.target();
    				tnodeList.add(tNodeSource);
    				if(tNodeTarget.toString().contains("bool")){
    					int tSourceIndex=IndexOfNodeInANac_PSO(nac, tNodeSource);
	    				NegEQU_Count+=nac.ANacEqualNodes.get(tSourceIndex).HEList.size();
    				}else{
	    				tnodeList.add(tNodeTarget);
	    				int tSourceIndex=IndexOfNodeInANac_PSO(nac, tNodeSource);
	    				if(tSourceIndex==-1)
	    					continue;
	    				int tTargetIndex=IndexOfNodeInANac_PSO(nac, tNodeTarget);
	    				if(tTargetIndex==-1)
	    					continue;
	    				ExploringItemPSO.NacEqualNode tSourceEqualNode=nac.ANacEqualNodes.get(tSourceIndex);
	    				ExploringItemPSO.NacEqualNode tTargetEqualNode=nac.ANacEqualNodes.get(tTargetIndex);
	    				for(int k=0;k<=tSourceEqualNode.HEList.size()-1;k++){
	    					String hNodeSource=tSourceEqualNode.HEList.get(k);
	    					for(int q=0;q<=tTargetEqualNode.HEList.size()-1;q++){
	    						String hNodeTarget=tTargetEqualNode.HEList.get(q);
	    						if(isExistsEdgeWithLabel_PSO(HedgeList,hNodeSource, hNodeTarget, tEdge.label().toString())){
	    							NegEQU_Count++;
	    						}
	    					}
	    				}
    				}
    			}
    		}
    		
    	
    	}
       	////////////////////////////////////////////////
     	return EQU_Count-NegEQU_Count;
    }
	private boolean isExistsEdgeWithLabel_PSO(ArrayList<HostEdge>  HedgeList,String hNodeSource,String hNodeTarget,String label){
    	for(int i=0;i<=HedgeList.size()-1;i++){
    		HostEdge hEdge=HedgeList.get(i);
    		if(hEdge.source().toString().equals(hNodeSource) && hEdge.target().toString().equals(hNodeTarget) && hEdge.label().toString().equals(label))
    			return true;
    	}
    	return false;
    }
    private void searchNacEquallNodes_PSO(ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList,ExploringItemPSO exploringItemPSO,int NacIndex){
    	ExploringItemPSO.NAC nac=exploringItemPSO.allNACs.get(NacIndex);
    	nac.ANacEqualNodes.clear();
    	for(int i=0;i<=nac.rulenodeList.size()-1;i++){
    		ExploringItemPSO.NacEqualNode nacEqualNode=null;
    		RuleNode tNode=nac.rulenodeList.get(i);
    		if(tNode.toString().contains("bool"))
    			continue;
    		for(int j=0;j<=HnodeList.size()-1;j++){
    			String hNode=HnodeList.get(j);
    			boolean isContinue=true;
    			for(int k=0;k<=nac.ruleedgeList.size()-1 && isContinue;k++){
        			RuleEdge tEdge=nac.ruleedgeList.get(k);
        			if(tEdge.isLoop() && tEdge.source().equals(tNode)){
        				boolean isFind=false;
        				for(int p=0;p<=HedgeList.size()-1;p++){
        					HostEdge hEdge=HedgeList.get(p);
        					if(hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode)){
        						isFind=true;
        						break;
        					}
        				}
        				isContinue=isFind;
        			}else if(!tEdge.isLoop() && tEdge.source().equals(tNode) && tEdge.target().toString().contains("bool")){
        				boolean isFind=false;
        				for(int p=0;p<=HedgeList.size()-1;p++){
        					HostEdge hEdge=HedgeList.get(p);
        					if(!hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode) && hEdge.target().toString().contains(tEdge.target().toString())){
        						isFind=true;
        						break;
        					}
        				}
        				isContinue=isFind;
        			}
    			}
    			if(isContinue){
    				if(nacEqualNode==null)
    					nacEqualNode=exploringItemPSO.getNewNacEqualNode();
    				nacEqualNode.tNode=tNode;
    				nacEqualNode.HEList.add(hNode);
    			}
    		}
    		if(nacEqualNode!=null)
    			nac.ANacEqualNodes.add(nacEqualNode);
    	}
    	exploringItemPSO.allNACs.set(NacIndex,nac);    	
    }
    private boolean isSingleNode_PSO(ExploringItemPSO.NAC nac,RuleNode tNode){
    	boolean isSingle=true;
    	for(int q=0;q<=nac.ruleedgeList.size()-1;q++){
			RuleEdge tEdge=nac.ruleedgeList.get(q);
			if(!tEdge.isLoop() && (tEdge.source().equals(tNode) || tEdge.target().equals(tNode))){
				isSingle=false;
				break;
			}
		}
    	return isSingle;
    }
 
    private int IndexOfNodeInANac_PSO(ExploringItemPSO.NAC nac,RuleNode tNode){
      	for(int i=0;i<=nac.ANacEqualNodes.size()-1;i++)
    		if(nac.ANacEqualNodes.get(i).tNode.equals(tNode)){
    			return i;
    		}
    	return -1;
    }
	

    
    
////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
/////////////////////Model Checking by "A*" ||  "IDA*" ||  "BeamSearch"/////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

    @SuppressWarnings("unchecked")
	public GraphState heuristicIDAdoNext(ExploringItemIDA exploringItems) {
    	//exploringItems.typeOfAlg="A*" ||  "IDA*" ||  "BeamSearch"
    	
    	if(exploringItems.typeOfAlg.equals("A*"))
    		heuristicAstar(exploringItems);
    	if(exploringItems.typeOfAlg.equals("IDA*"))
    		heuristicIDAstar(exploringItems);
    	if(exploringItems.typeOfAlg.equals("BeamSearch"))
    		heuristicBeamSearch(exploringItems);
    	return null;
	}

    ///////////////////////////A* /////////////////////////////////////////
    public void heuristicAstar(ExploringItemIDA exploringItems){
    	/*
    	 * • Input:
				– QUEUE: Path only containing root
			• Algorithm:
				– WHILE (QUEUE not empty && first path not reach goal) DO
					• Remove first path from QUEUE
					• Create paths  to all children
					• Reject paths with loops
					• Add paths and sort QUEUE (by f = cost + heuristic)
					• IF QUEUE contains paths: P, Q
							AND P ends in node Ni && Q contains node Ni
							AND cost_P <= cost_Q  !!We have reversed this condition!!!
							THEN remove P
				– IF goal reached THEN success ELSE failure
    	 */
    	
    	
    	exploringItems.allPaths.clear();
    	
    	GraphState initialState=getNextState();   //get from poll
  		GraphState curstate = initialState;
      	transientStack.clear();
      	clearPool();
    	
    	ExploringItemIDA.StateRule staterule=exploringItems.getNewStateRule();
    	staterule.state=initialState;
    	staterule.ruleName="";
    	staterule.outTransSize=curstate.getMatches().size();
    	ExploringItemIDA.Path curpath=exploringItems.getNewPath();
    	curpath.items.add(staterule);
    	curpath.f=find_f_path(exploringItems, curpath);
    	exploringItems.allPaths.add(curpath);
    	exploringItems.Number_Explored_States=1;
    	while(exploringItems.allPaths.size()>0 && exploringItems.heuristicResult==null){
    		curpath=exploringItems.allPaths.get(0);
    		exploringItems.allPaths.remove(0);
    		curstate=curpath.items.get(curpath.items.size()-1).state;  //last state of path
    		List<MatchResult> matches = curpath.items.get(curpath.items.size()-1).state.getMatches();
    		   		
    		Set<? extends GraphTransition> curstateOutTrans= curstate.getTransitions();
    		
    		if(matches.size()==0  && curstateOutTrans.size()==0 ){
				if(exploringItems.CTLproperty.equals("deadlock")){
					heuristicResult="reachability";
					exploringItems.heuristicResult="reachability";
					exploringItems.First_Found_Dead_depth=curpath.items.size()-1;
					exploringItems.lastStateInReachability=curstate;
					exploringItems.witORcountPath=curpath;
					break;
				}
			}
    		else{
				if(ISstateHasMCtarget_IDABS(exploringItems,curstate)){
					exploringItems.heuristicResult="reachability";
					exploringItems.First_Found_Dead_depth=curpath.items.size()-1;
					exploringItems.lastStateInReachability=curstate;
					exploringItems.witORcountPath=curpath;
					break;
				}
			}
    		
    		
    		if(matches.size()!=0){
        		ArrayList<GraphState> allstates=new ArrayList<GraphState>();
        		for (MatchResult next : matches){
        			RuleTransition ruletransition=null;
					try {
						ruletransition = curstate.applyMatch(next);
					} catch (InterruptedException e) {
						// do nothing
						e.printStackTrace();
					}            //call putInPool(resultState)
        			setNextState();
        			GraphState childstate=getNextState();
        			if(childstate!=null)
        				exploringItems.Number_Explored_States++;
        			if(childstate==null && ruletransition!=null)
        				childstate=ruletransition.target();
        			if(childstate!=null && childstate.getNumber()>curstate.getNumber() && !allstates.contains(childstate) && !IsCreateCycleWithNewState(curpath,childstate)){
        				allstates.add(childstate);
        				staterule=exploringItems.getNewStateRule();
              	    	staterule.state=childstate;
              	    	staterule.ruleName=next.toString();
              	    	staterule.outTransSize=childstate.getMatches().size();
              	    	ExploringItemIDA.Path newpath=AddNewStateToLastAndCopy(exploringItems, curpath, staterule);
              	    	exploringItems.allPaths.add(newpath);
          			}
          		} 
    		}else if(curstateOutTrans.size()!=0){
    			for (GraphTransition next : curstateOutTrans){
    				GraphState childstate=next.target();
    				if(childstate!=null && childstate.getNumber()>curstate.getNumber() && !IsCreateCycleWithNewState(curpath,childstate)){
        				staterule=exploringItems.getNewStateRule();
              	    	staterule.state=childstate;
              	    	staterule.ruleName=next.toString();
              	    	if(childstate.getMatches().size()>0)
              	    		staterule.outTransSize=childstate.getMatches().size();
              	    	else
              	    		staterule.outTransSize=childstate.getTransitions().size();
              	    	ExploringItemIDA.Path newpath=AddNewStateToLastAndCopy(exploringItems, curpath, staterule);
              	    	exploringItems.allPaths.add(newpath);
          			}
    			}
    		}
    		
    		
    		sortPaths(exploringItems);
    		//purifyPaths(exploringItems);
    		removeExtraPaths(exploringItems);
    	}
    	
    	
   }
    ////////////////////////////////////////
    ////////////////////////////////////////
    public void removeExtraPaths(ExploringItemIDA exploringItems){
    	//Remove each path that its length is greater than maxDepthOfSearch
    	int i=exploringItems.allPaths.size()-1;
    	while(i>=0){
    		if(exploringItems.allPaths.get(i).items.size()-1>exploringItems.maxDepthOfSearch)
    			exploringItems.allPaths.remove(i);
    		i--;
    	}
    }
    public void purifyPaths(ExploringItemIDA exploringItems){
    	//IF QUEUE contains paths: P, Q
		//AND P ends in node Ni && Q contains node Ni
		//AND cost_P <= cost_Q 
    	//THEN remove P
    	///It is be noted that all paths have been sorted descendingly
    	for(int i=exploringItems.allPaths.size()-1;i>=1;i--){
    		ExploringItemIDA.Path Ppath=exploringItems.allPaths.get(i);
    		GraphState PlastState=Ppath.items.get(Ppath.items.size()-1).state;
    		boolean isFind=false;
    		for(int j=0;j<i;j++){
    			ExploringItemIDA.Path Qpath=exploringItems.allPaths.get(j);
    			for(int k=0;k<=Qpath.items.size()-1;k++)
    				if(Qpath.items.get(k).state.equals(PlastState)){
    					isFind=true; break;
    				}
    			if(isFind)
    				break;
    		}
    		if(isFind){
    			exploringItems.allPaths.remove(i);
    		}
    	}
    }
    
    public double find_f_path(ExploringItemIDA exploringItems,ExploringItemIDA.Path path){
    	double f=0;
    	if(exploringItems.CTLproperty.equals("deadlock")){  
    	   	if(exploringItems.typeOfHeuristic.equals("HEU_BLKRULESPATH")){
		    	//f(path)=numblockedInPath+1/(1+pathlen)
	    		f=1.0/(1+path.items.size()-1);
		    	for(int i=0;i<=path.items.size()-1;i++)
		    		f+=10*exploringItems.RulesCount-path.items.get(i).outTransSize;
	    	}else if(exploringItems.typeOfHeuristic.equals("HEU_BLKRULESSTATE")){
	    		//f(path)=numblockedInState+1/(1+pathlen)
	    		f=1.0/(1+path.items.size()-1);
	    		f+=10*exploringItems.RulesCount-path.items.get(path.items.size()-1).outTransSize;
	    	}
    	}else{  //reachability
    		GraphState state=path.items.get(path.items.size()-1).state;
    		Set<? extends HostEdge> Host_edgeSet=null;
			Host_edgeSet=state.getGraph().edgeSet();


        	ArrayList<HostEdge> HedgeList=new ArrayList<HostEdge>();
        	for(HostEdge he:Host_edgeSet)
        		HedgeList.add(he);  
        	
         	ArrayList<String> HnodeList=new ArrayList<String>();
         	for(HostEdge he:Host_edgeSet)
     			if(!HnodeList.contains(he.source().toString())){
     				HnodeList.add(he.source().toString());
     			}
           	f=findEQU_IDA(exploringItems,HedgeList,HnodeList);
    	}
    	
    	return f;
    	
    }
    
    public void sortPaths(ExploringItemIDA exploringItems){
		///////////////////////////////bubble sort///
		///sort based on path.f descendingly
    	
		boolean swapped = true;
		int j = 0;
		ExploringItemIDA.Path tmp;
		while (swapped){
			swapped = false;
			j++;
			for (int i = 0; i < exploringItems.allPaths.size() - j; i++) {
				if (exploringItems.allPaths.get(i).f < exploringItems.allPaths.get(i+1).f) {
				    tmp = exploringItems.allPaths.get(i);
				    exploringItems.allPaths.set(i, exploringItems.allPaths.get(i+1));
				    exploringItems.allPaths.set(i+1,tmp);
				    swapped = true;
				}
			}
		}

    }
    
    public ExploringItemIDA.Path AddNewStateToLastAndCopy(ExploringItemIDA exploringItems,ExploringItemIDA.Path origPath,ExploringItemIDA.StateRule newStaterule){
    	ExploringItemIDA.Path path=exploringItems.getNewPath();
    	for(int i=0;i<=origPath.items.size()-1;i++){
    		ExploringItemIDA.StateRule staterule=exploringItems.getNewStateRule();
    		staterule=origPath.items.get(i);
    		path.items.add(staterule);
    	}
    	path.items.add(newStaterule);
    	path.f=find_f_path(exploringItems, path);
    	return path;	
    }
    public boolean IsCreateCycleWithNewState(ExploringItemIDA.Path path,GraphState state){
    	boolean isExists=false;
    	for(int i=0;i<=path.items.size()-1;i++)
    		if(path.items.get(i).state.equals(state)){
    			isExists=true;
    			break;
    		}
    	return isExists;
    }
    private  boolean ISstateHasMCtarget_IDABS(ExploringItemIDA exploringItems,GraphState state){
    	
    	boolean isexists=false;
		
		ArrayList<QualName> Alltype=exploringItems.Alltype;
		
		List<MatchResult> matches=state.getMatches();
		boolean flag=true;
		
		if(exploringItems.CTLproperty.equals("deadlock")){
			if(matches.size()!=0){
				for (MatchResult next : matches) {
				        if(!Alltype.contains(QualName.name(next.toString()))){
				        	flag=false;
				        	break;
				        }
				        
				}
				isexists=flag;
			}else{
				Set<? extends GraphTransition> curstateOutTrans= state.getTransitions();
				for (GraphTransition next : curstateOutTrans) {
			        if(!Alltype.contains(QualName.name(next.toString()))){
			        	flag=false;
			        	break;
			        }
				}
				isexists=flag;
			}
		}else{   //reachability
			for (MatchResult next : matches) {
		        if(next.toString().equals(exploringItems.ModelCheckingTarget)){
		        	isexists=true;
		        	break;
		        }
		    }
		}
		return isexists;
	}
    ////////////////////////////////////////////////////////////////////
    ///////////////////////////IDA* /////////////////////////////////////////
    public void heuristicIDAstar(ExploringItemIDA exploringItems){
    	/*
    	 * IDA* Algorithm
			• f-bound=f(S0)  
			• Algorithm:
				– WHILE (goal is not reached) DO
					• f-bound =f-limitted_search(f-bound)

		  *  f-limitted Search Algorithm
			Input:
				– QUEUE : Path only containing root
				– f-bound
				– f-new =0  !!We have reversed this value!!!
			• Algorithm:
				– WHILE (QUEUE not empty && goal not reached) DO
					• Remove first path from QUEUE
					• Create paths to children
					• Reject paths with loops
					• Add paths with f(path) >= f-bound to front of QUEUE (depth-first)   !!We have reversed this condition!!!
					• f-new=maximum( {f-new} | {f(P) | P is rejected path} )   !!We have reversed the minimum!!!
				– IF goal reached THEN success ELSE report f-new
		*/
    	
    	GraphState initialState=getNextState();   //get from poll
  		GraphState curstate = initialState;
      	transientStack.clear();
      	clearPool();
    	exploringItems.Number_Explored_States=1;
       	exploringItems.allPaths.clear();
		ExploringItemIDA.StateRule staterule=exploringItems.getNewStateRule();
    	staterule.state=initialState;
    	staterule.ruleName="";
    	staterule.outTransSize=curstate.getMatches().size();
    	ExploringItemIDA.Path curpath=exploringItems.getNewPath();
    	curpath.items.add(staterule);
    	curpath.f=find_f_path(exploringItems, curpath);
    	double f_bound=curpath.f;
    	double f_new=0;
    	while(exploringItems.heuristicResult==null){
    		exploringItems.allPaths.clear();
    		staterule=exploringItems.getNewStateRule();
        	staterule.state=initialState;
        	staterule.ruleName="";
        	staterule.outTransSize=curstate.getMatches().size();
        	curpath=exploringItems.getNewPath();
        	curpath.items.add(staterule);
        	curpath.f=find_f_path(exploringItems, curpath);
        	exploringItems.allPaths.add(curpath);
        	f_new=0;
        	while(exploringItems.allPaths.size()>0 && exploringItems.heuristicResult==null){
        		curpath=exploringItems.allPaths.get(0);
        		exploringItems.allPaths.remove(0);
        		curstate=curpath.items.get(curpath.items.size()-1).state;  //last state of path
        		List<MatchResult> matches = curpath.items.get(curpath.items.size()-1).state.getMatches();
        		   		
        		Set<? extends GraphTransition> curstateOutTrans= curstate.getTransitions();
        		
        		if(matches.size()==0  && curstateOutTrans.size()==0 ){
    				if(exploringItems.CTLproperty.equals("deadlock")){
    					heuristicResult="reachability";
    					exploringItems.heuristicResult="reachability";
    					exploringItems.First_Found_Dead_depth=curpath.items.size()-1;
    					exploringItems.lastStateInReachability=curstate;
    					exploringItems.witORcountPath=curpath;
    					break;
    				}
    			}
        		else{
    				if(ISstateHasMCtarget_IDABS(exploringItems,curstate)){
    					exploringItems.heuristicResult="reachability";
    					exploringItems.First_Found_Dead_depth=curpath.items.size()-1;
    					exploringItems.lastStateInReachability=curstate;
    					exploringItems.witORcountPath=curpath;
    					break;
    				}
    			}
        		
        		if(matches.size()!=0){
            		ArrayList<GraphState> allstates=new ArrayList<GraphState>();
            		for (MatchResult next : matches){
            			RuleTransition ruletransition=null;
						try {
							ruletransition = curstate.applyMatch(next);
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}            //call putInPool(resultState)
            			setNextState();
            			GraphState childstate=getNextState();
            			if(childstate!=null)
            				exploringItems.Number_Explored_States++;
            			if(childstate==null && ruletransition!=null)
            				childstate=ruletransition.target();
            			if(childstate!=null && childstate.getNumber()>curstate.getNumber() && !allstates.contains(childstate) && !IsCreateCycleWithNewState(curpath,childstate)){
            				allstates.add(childstate);
            				staterule=exploringItems.getNewStateRule();
                  	    	staterule.state=childstate;
                  	    	staterule.ruleName=next.toString();
                  	    	staterule.outTransSize=childstate.getMatches().size();
                  	    	ExploringItemIDA.Path newpath=AddNewStateToLastAndCopy(exploringItems, curpath, staterule);
                  	    	if(exploringItems.CTLproperty.equals("deadlock")){
	                  	    	if(newpath.f>f_bound)
	                  	    		exploringItems.allPaths.add(0,newpath);
	                  	    	else if(newpath.f>f_new)
	                  	    		f_new=newpath.f;
                  	    	}else  //reachability
                  	    	{
                  	    		if(f_bound<0){
	                  	    		if(newpath.f>=f_bound)
		                  	    		exploringItems.allPaths.add(0,newpath);
		                  	    	else if(newpath.f>f_new)
		                  	    		f_new=newpath.f;
                  	    		}else{
                  	    			if(newpath.f>f_bound)
		                  	    		exploringItems.allPaths.add(0,newpath);
		                  	    	else if(newpath.f>f_new)
		                  	    		f_new=newpath.f;
                  	    		}
                  	    			
                  	    	}
              			}
              		} 
        		}else if(curstateOutTrans.size()!=0){
        			for (GraphTransition next : curstateOutTrans){
        				GraphState childstate=next.target();
        				if(childstate!=null && childstate.getNumber()>curstate.getNumber() && !IsCreateCycleWithNewState(curpath,childstate)){
        					staterule=exploringItems.getNewStateRule();
                  	    	staterule.state=childstate;
                  	    	staterule.ruleName=next.toString();
                  	    	if(childstate.getMatches().size()>0)
                  	    		staterule.outTransSize=childstate.getMatches().size();
                  	    	else
                  	    		staterule.outTransSize=childstate.getTransitions().size();
                  	    	ExploringItemIDA.Path newpath=AddNewStateToLastAndCopy(exploringItems, curpath, staterule);
                  	    	if(newpath.f>=f_bound)
                  	    		exploringItems.allPaths.add(0,newpath);
                  	    	else if(newpath.f>f_new)
                  	    		f_new=newpath.f;
              			}
        			}
        		}
        		        		       		
        		removeExtraPaths(exploringItems);
        	}  //End While
        	f_bound=f_new;
    	}
   }
    //////////////////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////Beam Search /////////////////////////////////////////
    public void heuristicBeamSearch(ExploringItemIDA exploringItems){
    	
    	//Beam search algorithm from A. Groce, W. Visser. "Heuristics for model checking Java programs", International Journal on Software Tools for Technology Transfer (STTT), vol. 6, no. 4, pp. 260-276, 2004. 
    	
    	exploringItems.allPaths.clear();
    	
    	GraphState initialState=getNextState();   //get from poll
  		GraphState curstate = initialState;
      	transientStack.clear();
      	clearPool();
    	
    	ExploringItemIDA.StateRule staterule=exploringItems.getNewStateRule();
    	staterule.state=initialState;
    	staterule.ruleName="";
    	staterule.outTransSize=curstate.getMatches().size();
    	ExploringItemIDA.Path curpath=exploringItems.getNewPath();
    	curpath.items.add(staterule);
    	curpath.f=find_f_path(exploringItems, curpath);
    	exploringItems.allPaths.add(curpath);
    	exploringItems.Number_Explored_States=1;
    	while(exploringItems.allPaths.size()>0 && exploringItems.heuristicResult==null){
    		exploringItems.allPathsTemp.clear();
    		while(exploringItems.allPaths.size()>0 && exploringItems.heuristicResult==null){
	    		curpath=exploringItems.allPaths.get(0);
	    		exploringItems.allPaths.remove(0);
	    		curstate=curpath.items.get(curpath.items.size()-1).state;  //last state of path
	    		List<MatchResult> matches = curpath.items.get(curpath.items.size()-1).state.getMatches();
	    		   		
	    		Set<? extends GraphTransition> curstateOutTrans= curstate.getTransitions();
	    		
	    		if(matches.size()==0  && curstateOutTrans.size()==0 ){
					if(exploringItems.CTLproperty.equals("deadlock")){
						heuristicResult="reachability";
						exploringItems.heuristicResult="reachability";
						exploringItems.First_Found_Dead_depth=curpath.items.size()-1;
						exploringItems.lastStateInReachability=curstate;
						exploringItems.witORcountPath=curpath;
						break;
					}
				}
	    		else{
					if(ISstateHasMCtarget_IDABS(exploringItems,curstate)){
						exploringItems.heuristicResult="reachability";
						exploringItems.First_Found_Dead_depth=curpath.items.size()-1;
						exploringItems.lastStateInReachability=curstate;
						exploringItems.witORcountPath=curpath;
						
						break;
					}
				}
	    		
	    		
	    		if(matches.size()!=0){
	        		ArrayList<GraphState> allstates=new ArrayList<GraphState>();
	        		for (MatchResult next : matches){
	        			RuleTransition ruletransition=null;
						try {
							ruletransition = curstate.applyMatch(next);
						} catch (InterruptedException e) {
							// do nothing
							e.printStackTrace();
						}            //call putInPool(resultState)
	        			setNextState();
	        			GraphState childstate=getNextState();
	        			if(childstate!=null)
	        				exploringItems.Number_Explored_States++;
	        			if(childstate==null && ruletransition!=null)
	        				childstate=ruletransition.target();
	        			if(childstate!=null && childstate.getNumber()>curstate.getNumber() && !allstates.contains(childstate) && !IsCreateCycleWithNewState(curpath,childstate)){
	        				allstates.add(childstate);
	        				staterule=exploringItems.getNewStateRule();
	              	    	staterule.state=childstate;
	              	    	staterule.ruleName=next.toString();
	              	    	staterule.outTransSize=childstate.getMatches().size();
	              	    	ExploringItemIDA.Path newpath=AddNewStateToLastAndCopy(exploringItems, curpath, staterule);
	              	    	exploringItems.allPathsTemp.add(newpath);
	          			}
	          		} 
	    		}else if(curstateOutTrans.size()!=0){
	    			for (GraphTransition next : curstateOutTrans){
	    				GraphState childstate=next.target();
	    				if(childstate!=null && childstate.getNumber()>curstate.getNumber() && !IsCreateCycleWithNewState(curpath,childstate)){
	        				staterule=exploringItems.getNewStateRule();
	              	    	staterule.state=childstate;
	              	    	staterule.ruleName=next.toString();
	              	    	if(childstate.getMatches().size()>0)
	              	    		staterule.outTransSize=childstate.getMatches().size();
	              	    	else
	              	    		staterule.outTransSize=childstate.getTransitions().size();
	              	    	ExploringItemIDA.Path newpath=AddNewStateToLastAndCopy(exploringItems, curpath, staterule);
	              	    	exploringItems.allPathsTemp.add(newpath);
	          			}
	    			}
	    		}
    		}
    		
    		//copy exploringItems.allPathsTemp To exploringItems.allPaths
    		for(int i=0;i<=exploringItems.allPathsTemp.size()-1;i++){
    			curpath=exploringItems.allPathsTemp.get(i);
    			exploringItems.allPaths.add(curpath);
    		}
    		   		
    		sortPaths(exploringItems);
    		removeExtraPaths_Beam(exploringItems);
    		
    	}
    	
    	//exploringItems.heuristicResult="reachability";
   }
    ////////////////////////////////////////
    ////////////////////////////////////////
    public void removeExtraPaths_Beam(ExploringItemIDA exploringItems){
    	//Remove each path that its length is greater than maxDepthOfSearch
    	int i=exploringItems.allPaths.size()-1;
    	while(i>=0){
    		if(exploringItems.allPaths.get(i).items.size()-1>exploringItems.maxDepthOfSearch)
    			exploringItems.allPaths.remove(i);
    		i--;
    	}
    	///Maintain the BeamWidth number of paths and throw a way the others!!!! 
    	
    	i=exploringItems.Beamwidth;
    	ArrayList<GraphState> allstates=new ArrayList<GraphState>();
    	i=0;
    	while(i<=exploringItems.allPaths.size()-1 && allstates.size()<exploringItems.Beamwidth){
    		GraphState gs=exploringItems.allPaths.get(i).items.get(exploringItems.allPaths.get(i).items.size()-1).state;
    		if(!allstates.contains(gs))
    			allstates.add(gs);
    		i++;
    	}
    	while(i<=exploringItems.allPaths.size()-1)
    		exploringItems.allPaths.remove(i);
    	   	
    }
    
    
    //////////////////////////////////////////////////
    //////////////////////////////////////////////////
	private int findEQU_IDA(ExploringItemIDA exploringItems,ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList){
		
		ArrayList<RuleEdge> TedgeList=exploringItems.targetGraph_edgeList;
    	ArrayList<RuleNode> TnodeList=exploringItems.targetGraph_nodeList;
    	///////////////////////////////////////////////////////////////
    	/////////////////////////////find positive equality////////////
    	//////////////////////////////////////////////////////////////
    	exploringItems.allinfo.clear();
    	for(int i=0;i<=TnodeList.size()-1;i++)    
    		for(int j=0;j<=HnodeList.size()-1;j++) {   
	    		Exploringinfo einfo=new Exploringinfo();
    			einfo.tnode=TnodeList.get(i).toString();
    			einfo.hnode=HnodeList.get(j).toString();
    			exploringItems.allinfo.add(einfo);
	        }
	      
    	for(int i=0;i<=exploringItems.allinfo.size()-1;i++){
    		Exploringinfo  einfo=exploringItems.allinfo.get(i);
    		String tn=einfo.tnode;
    		String hn=einfo.hnode;
    		int equall_count=0;
    		int tnode_edges_count=0;
    		
    		ArrayList<String> hedges=new ArrayList<String>();
    		
    		for(int k=0;k<=TedgeList.size()-1;k++){
    			RuleEdge ae=TedgeList.get(k);
    			if(ae.source().toString().equals(tn)){
    				tnode_edges_count++;
    				String tlabel=ae.label().toString();
    				for(int p=0;p<=HedgeList.size()-1;p++){
    					HostEdge he=HedgeList.get(p);
    					if(he.source().toString().equals(hn) && he.label().toString().equals(tlabel) && !hedges.contains(he.toString()))
    					{equall_count++;hedges.add(he.toString());break;}
    				}
    			}
    		}
    		einfo.equall_count=equall_count;
    		einfo.tnode_edges_count=tnode_edges_count;
    		einfo.diff=tnode_edges_count-equall_count;
    		if(einfo.diff==0 && i<exploringItems.allinfo.size()-1){
    			int j=i+1;
    			Exploringinfo  einfoo=exploringItems.allinfo.get(j);
    			while(j<=exploringItems.allinfo.size()-1){
    				if((einfoo.hnode.equals(hn) || einfoo.tnode.equals(tn) )){
    					exploringItems.allinfo.remove(j);
    					j=j;
    				}else
    					j++;
    				if(j<=exploringItems.allinfo.size()-1)
    					einfoo=exploringItems.allinfo.get(j);
    			}
    		}
    	}
    	
    	///////////////////////////////bubble sort///
    	///sort based on equall_count Descending (from greater to smaller)
    	
    	boolean swapped = true;
    	int p = 0;
    	Exploringinfo  tmp;
    	while (swapped){
    		swapped = false;
            p++;
            for (int i = 0; i < exploringItems.allinfo.size() - p; i++) {
            		if (exploringItems.allinfo.get(i).equall_count < exploringItems.allinfo.get(i+1).equall_count) {
                          tmp = exploringItems.allinfo.get(i);
                          exploringItems.allinfo.set(i, exploringItems.allinfo.get(i+1));
                          exploringItems.allinfo.set(i+1,tmp);
                          swapped = true;
                    }
              }
        }
    	//////////////////////////////
    	ArrayList<String> tnodes=new ArrayList<String>();
    	ArrayList<String> hnodes=new ArrayList<String>();
    	int EQU_Count=0;
    	for(int i=0;i<=exploringItems.allinfo.size()-1;i++){
    		Exploringinfo  einfo=exploringItems.allinfo.get(i);
    		String tn=einfo.tnode;
    		String hn=einfo.hnode;
    		if(!tnodes.contains(tn) && !hnodes.contains(hn)){
    			tnodes.add(tn);
    			hnodes.add(hn);
    			EQU_Count+=einfo.equall_count;
    		}
    	}
    		
    	
    	///////////////////////////////////////////////////////////////
    	/////////////////////////////find negative equality////////////
    	///////////////////////////////////////////////////////////////
    	if(exploringItems.allNACs==null)
    		return EQU_Count;
    	int NegEQU_Count=0;
    	@SuppressWarnings("unchecked")
		ArrayList<groove.verify.ExploringItemIDA.NAC> allNACs= (ArrayList<groove.verify.ExploringItemIDA.NAC>) exploringItems.allNACs.clone();
    	for(int i=0;i<=exploringItems.allNACs.size()-1;i++){
    		searchNacEquallNodes_IDA(HedgeList, HnodeList, exploringItems, i);
    		ExploringItemIDA.NAC nac=allNACs.get(i);
    		if(nac.ANacEqualNodes.size()==0)
    			continue;
    		ArrayList<RuleNode> tnodeList=new ArrayList<RuleNode>();
    		for(int j=0;j<=nac.ruleedgeList.size()-1;j++){
    			RuleEdge tEdge=nac.ruleedgeList.get(j);
    			RuleNode tNode=tEdge.source();
    			if(tEdge.isLoop() && isSingleNode_IDA(nac,tNode) && !tnodeList.contains(tNode)){
    				int tIndex=IndexOfNodeInANac_IDA(nac, tNode);
    				NegEQU_Count+=nac.ANacEqualNodes.get(tIndex).HEList.size();
    				tnodeList.add(tNode);
    			}else if(!tEdge.isLoop()){
    				RuleNode tNodeSource=tEdge.source();
    				RuleNode tNodeTarget=tEdge.target();
    				tnodeList.add(tNodeSource);
    				if(tNodeTarget.toString().contains("bool")){
    					int tSourceIndex=IndexOfNodeInANac_IDA(nac, tNodeSource);
	    				NegEQU_Count+=nac.ANacEqualNodes.get(tSourceIndex).HEList.size();
    				}else{
	    				tnodeList.add(tNodeTarget);
	    				int tSourceIndex=IndexOfNodeInANac_IDA(nac, tNodeSource);
	    				if(tSourceIndex==-1)
	    					continue;
	    				int tTargetIndex=IndexOfNodeInANac_IDA(nac, tNodeTarget);
	    				if(tTargetIndex==-1)
	    					continue;
	    				ExploringItemIDA.NacEqualNode tSourceEqualNode=nac.ANacEqualNodes.get(tSourceIndex);
	    				ExploringItemIDA.NacEqualNode tTargetEqualNode=nac.ANacEqualNodes.get(tTargetIndex);
	    				for(int k=0;k<=tSourceEqualNode.HEList.size()-1;k++){
	    					String hNodeSource=tSourceEqualNode.HEList.get(k);
	    					for(int q=0;q<=tTargetEqualNode.HEList.size()-1;q++){
	    						String hNodeTarget=tTargetEqualNode.HEList.get(q);
	    						if(isExistsEdgeWithLabel_GA(HedgeList,hNodeSource, hNodeTarget, tEdge.label().toString())){
	    							NegEQU_Count++;
	    						}
	    					}
	    				}
    				}
    			}
    		}
    		
    	
    	}
       	////////////////////////////////////////////////
     	return EQU_Count-NegEQU_Count;
    }
	private boolean isExistsEdgeWithLabel_IDA(ArrayList<HostEdge>  HedgeList,String hNodeSource,String hNodeTarget,String label){
    	for(int i=0;i<=HedgeList.size()-1;i++){
    		HostEdge hEdge=HedgeList.get(i);
    		if(hEdge.source().toString().equals(hNodeSource) && hEdge.target().toString().equals(hNodeTarget) && hEdge.label().toString().equals(label))
    			return true;
    	}
    	return false;
    }
    private void searchNacEquallNodes_IDA(ArrayList<HostEdge>  HedgeList,ArrayList<String> HnodeList,ExploringItemIDA exploringItems,int NacIndex){
    	ExploringItemIDA.NAC nac=exploringItems.allNACs.get(NacIndex);
    	nac.ANacEqualNodes.clear();
    	for(int i=0;i<=nac.rulenodeList.size()-1;i++){
    		ExploringItemIDA.NacEqualNode nacEqualNode=null;
    		RuleNode tNode=nac.rulenodeList.get(i);
    		if(tNode.toString().contains("bool"))
    			continue;
    		for(int j=0;j<=HnodeList.size()-1;j++){
    			String hNode=HnodeList.get(j);
    			boolean isContinue=true;
    			for(int k=0;k<=nac.ruleedgeList.size()-1 && isContinue;k++){
        			RuleEdge tEdge=nac.ruleedgeList.get(k);
        			if(tEdge.isLoop() && tEdge.source().equals(tNode)){
        				boolean isFind=false;
        				for(int p=0;p<=HedgeList.size()-1;p++){
        					HostEdge hEdge=HedgeList.get(p);
        					if(hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode)){
        						isFind=true;
        						break;
        					}
        				}
        				isContinue=isFind;
        			}else if(!tEdge.isLoop() && tEdge.source().equals(tNode) && tEdge.target().toString().contains("bool")){
        				boolean isFind=false;
        				for(int p=0;p<=HedgeList.size()-1;p++){
        					HostEdge hEdge=HedgeList.get(p);
        					if(!hEdge.isLoop() && hEdge.label().toString().equals(tEdge.label().toString()) && hEdge.source().toString().equals(hNode) && hEdge.target().toString().contains(tEdge.target().toString())){
        						isFind=true;
        						break;
        					}
        				}
        				isContinue=isFind;
        			}
    			}
    			if(isContinue){
    				if(nacEqualNode==null)
    					nacEqualNode=exploringItems.getNewNacEqualNode();
    				
    				nacEqualNode.tNode=tNode;
    				nacEqualNode.HEList.add(hNode);
    			}
    		}
    		if(nacEqualNode!=null)
    			nac.ANacEqualNodes.add(nacEqualNode);
    	}
    	exploringItems.allNACs.set(NacIndex,nac);    	
    }
    private boolean isSingleNode_IDA(ExploringItemIDA.NAC nac,RuleNode tNode){
    	boolean isSingle=true;
    	for(int q=0;q<=nac.ruleedgeList.size()-1;q++){
			RuleEdge tEdge=nac.ruleedgeList.get(q);
			if(!tEdge.isLoop() && (tEdge.source().equals(tNode) || tEdge.target().equals(tNode))){
				isSingle=false;
				break;
			}
		}
    	return isSingle;
    }
 
    private int IndexOfNodeInANac_IDA(ExploringItemIDA.NAC nac,RuleNode tNode){
      	for(int i=0;i<=nac.ANacEqualNodes.size()-1;i++)
    		if(nac.ANacEqualNodes.get(i).tNode.equals(tNode)){
    			return i;
    		}
    	return -1;
    }


/////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////


    
    @Override
    protected void prepare(GTS gts, GraphState state, Acceptor acceptor) {
        super.prepare(gts, state, acceptor);
        // for the closing strategy, there is no problem in aliasing
        // the graph data structures. On the whole, this seems wise, to
        // avoid excessive garbage collection.
        // gts.getRecord().setCopyGraphs(true);
        gts.addLTSListener(this.exploreListener);
        clearPool();
    }

    @Override
    public void finish() {
        super.finish();
        getGTS().removeLTSListener(this.exploreListener);
    }

    @Override
    protected GraphState computeNextState() {
        if (this.transientStack.isEmpty()) {
            return getFromPool();
        } else {
            return this.transientStack.pop();
        }
    }

    /** Adds a given state to the set of explorable states. */
    private void addExplorable(GraphState state) {
        if (state.isTransient()) {
            ClosingStrategy.this.transientStack.push(state);
        } else {
            putInPool(state);
        }
    }

    /** Callback method to retrieve the next element from the pool.
     * @return the next element, or {@code null} when the exploration is done.
     */
    abstract protected GraphState getFromPool();

    /** Callback method to add a non-transient graph state to the pool. */
    abstract protected void putInPool(GraphState state);

    /** Clears the pool, in order to prepare the strategy for reuse. */
    abstract protected void clearPool();

    /** Listener to keep track of states added to the GTS. */
    private final ExploreListener exploreListener = new ExploreListener();

    /** Local stack of transient states; these should be explored first. */
    private final Stack<GraphState> transientStack = new Stack<>();

    /** A queue with states to be explored, used as a FIFO. */
    private class ExploreListener implements GTSListener {
        @Override
        public void addUpdate(GTS gts, GraphState state) {
            addExplorable(state);
        }
    }
}
