package groove.gui.dialog;


import groove.explore.Exploration;
import groove.grammar.QualName;
import groove.grammar.aspect.AspectEdge;


import groove.grammar.model.GrammarModel;
import groove.grammar.model.ResourceKind;
import groove.grammar.model.RuleModel;

import groove.gui.Icons;

import groove.gui.Simulator;

import groove.gui.layout.SpringUtilities;
import groove.util.parse.FormatException;
import groove.verify.ExploringGaBayesNet;
import groove.verify.HeuBOA;














import java.awt.Color;
import java.awt.Cursor;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

import java.awt.event.KeyEvent;


import java.util.ArrayList;


import java.util.Iterator;

import java.util.Set;


import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;

import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTextField;
import javax.swing.KeyStroke;
import javax.swing.SpringLayout;

 /**
 *  @author Einollah Pira & Vahid Rafe
 *  
 */
public class HeuBOADialog extends JDialog  {

	private static final String START_COMMAND = "Start";
	private static final String Make_Knowlege_Base_COMMAND = "Make Knowlege Base";
	private static final String Enable_HostGraph_COMMAND = "Enable the Selected HostGraph";
	private static final String Explore_COMMAND = "Explore State Space";
	
	
    private static final String CANCEL_COMMAND = "Exit";

    private static final String START_TOOLTIP =
        "Restart with the customized exploration";
    
    private static final String Make_knowlege_base_TOOLTIP =
            "Make Knowlege Base...";
    
    
    private static final String Enable_HostGraph_TOOLTIP =
            "Enable The Selected HostGraph...";
    
    private static final String Explore_TOOLTIP =
            "Explore The State Space...";
    
    private static final String DEFAULT_TOOLTIP =
        "Set the currently selected exploration as the default for this grammar";
   

    /**
     * Color to be used for headers on the dialog.
     */
    public static final String HEADER_COLOR = "green";
    /**
     * Color to be used for text in the info panel.
     */
    public static final String INFO_COLOR = "#005050";
    /**
     * Color to be used for the background of the info panel.
     */
    public static final Color INFO_BG_COLOR = new Color(230, 230, 255);
    /**
     * Color to be used for the background boxes on the info panel.
     */
    public static final Color INFO_BOX_BG_COLOR = new Color(210, 210, 255);

    /**
     * Create the dialog.
     * @param simulator - reference to the simulator
     * @param owner - reference to the parent GUI component
     * @throws FormatException
     */
    public HeuBOADialog(Simulator simulator, JFrame owner) {
    	
    	AllreportTime=0;
    	this.simulator=simulator;
    	//Create the content panel.
        JPanel dialogContent = new JPanel(new SpringLayout());
       
        // dialogContent.setBorder(BorderFactory.createEmptyBorder(10, 400, 400, 400));
        KeyStroke escape = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
        KeyStroke enter = KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, 0);
        dialogContent.registerKeyboardAction(createCloseListener(), escape,
            JComponent.WHEN_IN_FOCUSED_WINDOW);
        dialogContent.registerKeyboardAction(createCloseListener(), enter,
            JComponent.WHEN_IN_FOCUSED_WINDOW);
        
        

        
       
        
        JLabel jl=new JLabel("All Host Graphs");
        dialogContent.add(jl);
        
        cmbHostGraph= new JComboBox();
        cmbHostGraph.setBackground(INFO_BOX_BG_COLOR);
        dialogContent.add(cmbHostGraph);
        
        GrammarModel grammermodel=simulator.getModel().getGrammar();
        Set<QualName> sname= grammermodel.getNames(ResourceKind.HOST);
       	Iterator<QualName> it=sname.iterator();
       	while(it.hasNext())
       	{
       		QualName ts=it.next();
       		cmbHostGraph.addItem(ts);
       	}
     
        
       	dialogContent.add(createEnableHostgraphPanel());
     
       	dialogContent.add(createRBmodelcheckingPanel());
       
             	
       	dialogContent.add(createBOATypePanel());
       	
       
       	
    	dialogContent.add(createSelectTypePanel());
    	
    	
    	
       	
        dialogContent.add(createModelChecking());
       	
       	
        
        dialogContent.add(createBOAparamsPanel());
        
        
        dialogContent.add(createContinuePanel());
        
    	
        dialogContent.add(createStartPanel());
        
        
        JLabel line4=new JLabel("------------------------------------------------------------------------------------");
    	line4.setForeground(Color.green);
    	dialogContent.add(line4);
        
        JLabel jstep4=new JLabel("The Result of Model Checking");
        jstep4.setForeground(Color.blue);
        dialogContent.add(jstep4);
        
        txtresultOfmodelchecking=new JTextField("");
        txtresultOfmodelchecking.setForeground(INFO_BOX_BG_COLOR);
        txtresultOfmodelchecking.setEnabled(false);
        dialogContent.add(txtresultOfmodelchecking);
        
        JLabel jstep5=new JLabel("Total running time, Number of explored states , First found goal state depth, Number of fitness function calls, Running time of fitness evaluations");
          jstep5.setForeground(Color.blue);
         dialogContent.add(jstep5);
         
        txtTimeSpent=new JTextField(" ");
        txtTimeSpent.setForeground(INFO_BOX_BG_COLOR);
        txtTimeSpent.setEnabled(false);
        dialogContent.add(txtTimeSpent);
        
        
        
        lblResultsOfAllGoals=new JLabel("Results of all found goal states: after passing time -- depth");
        lblResultsOfAllGoals.setForeground(Color.blue);
        dialogContent.add(lblResultsOfAllGoals);
        txtResultsOfAllGoals=new JTextField("");
        
        
        
        txtResultsOfAllGoals.setEnabled(true);
        dialogContent.add(txtResultsOfAllGoals);
        
        lblResultsOfAllGoals.setVisible(false);
  		txtResultsOfAllGoals.setVisible(false);
        
        
        dialogContent.add(createCancelPanel());
        
        manageRB();
        
        SpringUtilities.makeCompactGrid(dialogContent, 18, 1, 5, 5, 15, 0);
        // Add the dialogContent to the dialog.
        add(dialogContent);
        setTitle("Model Checking by Bayesian Optimization Algorithm...");
        setIconImage(Icons.GROOVE_ICON_16x16.getImage());
        setSize(1155, 690);  //width  height
        //pack();
        setLocationRelativeTo(owner);
        
        /////
        EnableHostGraphButton.setEnabled(true);
        startButton.setEnabled(false);
        ////
        
        
        setVisible(true);
        
     }
    /**
     * Creates the button panel.
     */
    
    
    private JPanel createContinuePanel() {
    	JPanel buttonPanel = new JPanel();
    	chbContinue=new JCheckBox("Continue after finding a goal state           ");
    	
    	chbContinue.addItemListener(new ItemListener() {
            public void itemStateChanged(ItemEvent e) {             
           	 if(chbContinue.isSelected()){
           		 lblResultsOfAllGoals.setVisible(true);
           		 txtResultsOfAllGoals.setVisible(true);
           	 }else{
           		 lblResultsOfAllGoals.setVisible(false);
           		 txtResultsOfAllGoals.setVisible(false);
           	 }
            }           
         });
    	
    	buttonPanel.add(chbContinue);
    	
    	JLabel jl=new JLabel("Time limit (sec): ");
    	buttonPanel.add(jl);
    	txtTimeLimit=new JTextField("100               ");
    	buttonPanel.add(txtTimeLimit);
    	
    	
        return buttonPanel;
    	
    }
    
      private JPanel createRBmodelcheckingPanel() {
    	JPanel buttonPanel = new JPanel();
    	rbdeadlock=new JRadioButton("Deadlock (EF q)");
    	rbreachability=new JRadioButton("Reachabiliy (EF q)");
    	rbsafety=new JRadioButton("Refutation of Safety (AG !q)");
    	rbLiveness=new JRadioButton("Refutation of Liveness");
    	
    	rbdeadlock.setSelected(true);
    	
    	rbdeadlock.addItemListener(new ItemListener() {
            public void itemStateChanged(ItemEvent e) {             
           	 manageRB();
            }           
         });
   	
	   	rbreachability.addItemListener(new ItemListener() {
	           public void itemStateChanged(ItemEvent e) {             
	          	 manageRB();
	           }           
	     });
	   	
	   	rbsafety.addItemListener(new ItemListener() {
	           public void itemStateChanged(ItemEvent e) {             
	          	 manageRB();
	           }           
	     });
   	
	   	rbLiveness.addItemListener(new ItemListener() {
	           public void itemStateChanged(ItemEvent e) {             
	          	 manageRB();
	           }           
	     });
    	
    	buttonPanel.add(rbdeadlock);
    	buttonPanel.add(rbreachability);
    	buttonPanel.add(rbsafety);
    	buttonPanel.add(rbLiveness);
    	
    	ButtonGroup options = new ButtonGroup();
    	options.add(rbdeadlock);
    	options.add(rbreachability);
    	options.add(rbsafety);
    	options.add(rbLiveness);
    	
    	//////////////////////////////////////
    	//rbdeadlock.setVisible(false);
    	//rbsafety.setVisible(false);
    	rbLiveness.setVisible(false);
    	//rbreachability.setSelected(true);
    	//buttonPanel.setVisible(false);
    	///////////////////////////////////////
        return buttonPanel;
    }
    private JPanel createBOATypePanel() {

    	//JPanel buttonPanel = new JPanel(new SpringLayout());
    	
    	JPanel buttonPanel = new JPanel();
    	
    	buttonPanel.setBackground(new Color(200, 200, 200));
    	
    	
    	rbIS_nBOA=new JRadioButton("BOAcl2 (BOA with Naive Bayes Network)");
    	rbIS_cBOA=new JRadioButton("BOAcln (BOA with Chain Bayes Network)");
    	rbIS_tpBOA=new JRadioButton("BOActp (BOA with Chain Bayes Network in which each node has two parents)");
    	rbIS_3pBOA=new JRadioButton("3pBOA (BOA with Chain Bayes Network in which each node has three parents)");
    	rbIS_4pBOA=new JRadioButton("4pBOA (BOA with Chain Bayes Network in which each node has four parents)");
    	
    	
    	
    	
    	
    	buttonPanel.add(rbIS_nBOA);
    	buttonPanel.add(rbIS_cBOA);
    	buttonPanel.add(rbIS_tpBOA);
    	//buttonPanel.add(rbIS_3pBOA);
    	//buttonPanel.add(rbIS_4pBOA);
   
    	
    	rbIS_nBOA.setSelected(true);
    	
    	
    	ButtonGroup options = new ButtonGroup();
    
    	options.add(rbIS_nBOA);
    	options.add(rbIS_cBOA);
    	options.add(rbIS_tpBOA);
    	//options.add(rbIS_3pBOA);
    	//options.add(rbIS_4pBOA);
    	
    	//SpringUtilities.makeCompactGrid(buttonPanel, 6, 1, 5, 5, 15, 0);
    	
    	//SpringUtilities.makeCompactGrid(buttonPanel, 3, 1, 5, 5, 15, 0);
    	
    	return buttonPanel;
    	
    
    }
    private JPanel createSelectTypePanel() {
    	JPanel buttonPanel = new JPanel();
    	rbTruncation=new JRadioButton("Truncation");
    	rbTournament=new JRadioButton("Tournament (with size=4)");
    	
    	
    	rbTruncation.setSelected(true);
    	
    	JLabel jl=new JLabel("The Selection Method:      ");
    	buttonPanel.add(jl);
    	
    	buttonPanel.add(rbTruncation);
    	buttonPanel.add(rbTournament);
    	
    	
    	ButtonGroup options = new ButtonGroup();
    	options.add(rbTruncation);
    	options.add(rbTournament);
        return buttonPanel;
    	
    }
    
    private int RulesCount;
    public ArrayList<QualName> RulesName;
    
    
    private JCheckBox chbContinue;
    private JLabel lblResultsOfAllGoals;
    private JTextField txtResultsOfAllGoals;
    
    private JPanel createModelChecking(){
    	JPanel buttonPanel = new JPanel();
    	buttonPanel.add(new JLabel("The state property q:"));
        
    	cmbModelCheckingType=new JComboBox();
    	cmbModelCheckingType.setBackground(INFO_BOX_BG_COLOR);
    	buttonPanel.add(cmbModelCheckingType);
    	
    	Alltype=new ArrayList<QualName>();
    	
    	RulesCount=0;
    	RulesName=new ArrayList<QualName>();
    	
    	GrammarModel grammermodel=simulator.getModel().getGrammar();
        Set<QualName> sname= grammermodel.getNames(ResourceKind.RULE);
       
       	Iterator<QualName> it=sname.iterator();
       	while(it.hasNext())
       	{
       		    QualName ts=it.next();
        		RuleModel rulemodel=grammermodel.getRuleModel(ts);
	        	if(rulemodel.isEnabled()){
	        		Set<? extends AspectEdge> edgeSet=rulemodel.getSource().edgeSet();
	   
	        		boolean flag=false;
	        		for(AspectEdge ae:edgeSet ){
	        			//	        			if(ae.toString().contains("new:") ||ae.toString().contains("del:") || ae.toString().contains("not:") ){
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
	        				e.printStackTrace();
	        			}
	        		}
	        		
	        		if(!flag){
	        			cmbModelCheckingType.addItem(ts);
	        			Alltype.add(ts);
	        		}
	        		else{
	        			RulesCount++;
	        			RulesName.add(ts);
	        			
	        		}
	        			
	        	}
	       	}
       		cmbModelCheckingType.addItem("DeadLock");
       		
       		///////////////////////////////
       		//cmbModelCheckingType.setSelectedItem("DeadLock");
       		//cmbModelCheckingType.setEnabled(false);
       		///////////////////////////////
       		
       		return buttonPanel;
    }
    
  
    
    
    private JPanel createStartPanel() {
        JPanel buttonPanel = new JPanel();
        buttonPanel.add(getStartButton());
        return buttonPanel;
    }
    private JPanel createCancelPanel() {
        JPanel buttonPanel = new JPanel();
        buttonPanel.add(getCancelButton());
        return buttonPanel;
    }

   
   
    
    private JPanel createEnableHostgraphPanel() {
    	JPanel buttonPanel = new JPanel();
    	buttonPanel.add(getEnableHostGraphButton());
        return buttonPanel;
    }
    
    private void manageRB(){

    	if(startButton!=null){
    		cmbModelCheckingType.removeAllItems();
        	cmbModelCheckingType.setEnabled(true);
    		
        	
        	if(rbdeadlock.isSelected() || rbsafety.isSelected() || rbLiveness.isSelected()){
        		cmbModelCheckingType.addItem("DeadLock");
        		
        		cmbModelCheckingType.setEnabled(false);
        		
        	}
        	if(rbreachability.isSelected()){
        		for(int i=0;i<=Alltype.size()-1;i++){
        			String s=Alltype.get(i).toString();
        			if(!s.contains("DeadLock") && !s.contains("Live") && !s.contains("live")){
        				cmbModelCheckingType.addItem(s);
        				
        			}
        				
        		}
        	}
        	
        	
        	if(cmbModelCheckingType.getItemCount()==0)
        		startButton.setEnabled(false);
        	else
        		startButton.setEnabled(true);
    	}
    	
    	
    }
    
    
    
    /**
     * Creates the Genetic panel.
     */
    private JPanel createBOAparamsPanel() {
        JPanel geneticPanel = new JPanel(new SpringLayout());
        geneticPanel.setBackground(new Color(200, 200, 200));
        
        
        
             
        geneticPanel.add(new JLabel("Population"));
        txtPopulation=new JTextField(10);
        txtPopulation.setText("40");
        geneticPanel.add(txtPopulation);
        
        
        geneticPanel.add(new JLabel("Iterations"));
        txtIterations=new JTextField(10);
        txtIterations.setText("100");
        geneticPanel.add(txtIterations);

        geneticPanel.add(new JLabel("Depth of Search(the length of each chromosome)"));
        txtDepthOfSearch=new JTextField(10);
        txtDepthOfSearch.setText("100");
        geneticPanel.add(txtDepthOfSearch);

        lblSelectionRate=new JLabel("Selection Rate");
        geneticPanel.add(lblSelectionRate);
        txtSelectionRate=new JTextField(10);
        txtSelectionRate.setText("0.4");
        geneticPanel.add(txtSelectionRate);

        lblReplacementRate=new JLabel("Replacement Rate");
        geneticPanel.add(lblReplacementRate);
        txtReplacementRate=new JTextField(10);
        txtReplacementRate.setText("0.5");
        geneticPanel.add(txtReplacementRate);

        SpringUtilities.makeCompactGrid(geneticPanel, 5, 2, 5, 5, 15, 0);
              
        return geneticPanel;
        
        
    	
	
        
    }


    
    private RefreshButton startButton;
    private RefreshButton cancelButton;
   
    private RefreshButton EnableHostGraphButton;
    
    
    
    
    
    private JTextField  txtPopulation;
    private JTextField txtIterations;
    private JTextField txtDepthOfSearch;
    private JTextField txtSelectionRate;
    private JTextField txtReplacementRate;
    
    private JLabel lblSelectionRate;
    private JLabel lblReplacementRate;
    
    
    private JTextField txtTimeLimit;
    
    private Simulator simulator;
    private HeuBOA heuristicreach;
    private JComboBox cmbModelCheckingType;
    
    private  JComboBox cmbHostGraph;
    
    private  JRadioButton rbdeadlock;
    private  JRadioButton rbreachability;
    private  JRadioButton rbsafety;
    private  JRadioButton rbLiveness;
    
    private JRadioButton rbTruncation;
    private JRadioButton rbTournament;
    
       
    private JTextField txtresultOfmodelchecking;
    private JTextField txtTimeSpent;
    
    

    private  JRadioButton rbIS_nBOA;
    private  JRadioButton rbIS_cBOA;
    private  JRadioButton rbIS_tpBOA;
    private  JRadioButton rbIS_3pBOA;
    private  JRadioButton rbIS_4pBOA;
    
    
    ArrayList<QualName> Alltype;
    
    
    
    public void FillModelCheckingType(ArrayList<String> alltype){
    	//cmbModelCheckingType.removeAll();
    	cmbModelCheckingType.removeAllItems();
    	for(int i=0;i<=alltype.size()-1;i++){
    		String s=alltype.get(i);
    		cmbModelCheckingType.addItem(s);
    		cmbModelCheckingType.setSelectedIndex(0);
    	}
    	cmbModelCheckingType.addItem("DeadLock");
    	
    	
    }
   
    
    /** Initialises and returns the start button. */
    private RefreshButton getStartButton() {
        if (this.startButton == null) {
            // Create the explore button (reference is needed when setting the
            // initial value of the (strategy/acceptor) editors.
            this.startButton = new RefreshButton(START_COMMAND) {
                @Override
                public void execute() {
                	
                	//if(heuristicreach==null)
                		heuristicreach=new HeuBOA();
                	
               	 	String ModelCheckingType;
               	 	ModelCheckingType=cmbModelCheckingType.getSelectedItem().toString();
               	 	
               	 	if(cmbModelCheckingType.getSelectedItem().toString().contains("Live") || cmbModelCheckingType.getSelectedItem().toString().contains("live")){
	         	    	ModelCheckingType="DeadLock";
               	 	}
               	 	
               	   
               	 	heuristicreach.simulator=simulator;
               	 	heuristicreach.ModelCheckingTarget=ModelCheckingType;
               	    
	                heuristicreach.CTLproperty ="reachability";
	               
	               
	             	String BOAType="naiveBOA";
	             	
	             	if(rbIS_tpBOA.isSelected())
	             		BOAType ="tpBOA";
	             	if(rbIS_3pBOA.isSelected())
	             		BOAType ="3pBOA";
	             	if(rbIS_4pBOA.isSelected())
	             		BOAType ="4pBOA";
	             	if(rbIS_cBOA.isSelected())
	             		BOAType ="chainBOA";
	             	if(rbIS_nBOA.isSelected())
	             		BOAType ="naiveBOA";
               	 	
               	 	
	             	String SelectionType="TRUNC";
	             	if(rbTruncation.isSelected())
	             		SelectionType ="TRUNC";
	             	if(rbTournament.isSelected())
	             		SelectionType ="TOUR";
	             	
	             	if(chbContinue.isSelected()){
	             		heuristicreach.isContinue=true;
	             		heuristicreach.timeLimit=Integer.parseInt(txtTimeLimit.getText().trim());
	             	}
	             	else
	             	{
	             		heuristicreach.isContinue=false;
	             		heuristicreach.timeLimit=0;
	             	}
	             	
	             	
               	 	txtresultOfmodelchecking.setText("");
               	 	txtTimeSpent.setText("");
               	 	
               		setCursor(new Cursor(Cursor.WAIT_CURSOR));
               	 	
               		heuristicreach.HostGraphName=cmbHostGraph.getSelectedItem().toString();
                	
                   	heuristicreach.simulator=simulator;
               	 	heuristicreach.CountOFpopulation=Integer.parseInt(txtPopulation.getText());
               	 	heuristicreach.CrossOverRate=Double.parseDouble(txtReplacementRate.getText());
               	 	heuristicreach.DepthOfSearch=Integer.parseInt(txtDepthOfSearch.getText());
               	 	heuristicreach.Iterations=Integer.parseInt(txtIterations.getText());
               	 	heuristicreach.MutationRate=Double.parseDouble(txtSelectionRate.getText());
               	 	
               	 	heuristicreach.ReplacementRate=Double.parseDouble(txtReplacementRate.getText());
               	 	heuristicreach.SelectionRate=Double.parseDouble(txtSelectionRate.getText());	
               	 	
               	 	long startTime = System.currentTimeMillis();
               	 	long lastTime=startTime+heuristicreach.timeLimit*1000;
               	 	heuristicreach.lastTime=lastTime;
                	
               	 	exploreGaBayesNet=new ExploringGaBayesNet();
               	 	heuristicreach.exploreGaBayesNet=exploreGaBayesNet;
                	String heuristicResult=heuristicreach.start(ModelCheckingType,BOAType,SelectionType,RulesCount,RulesName,null,null);
               	    
               	    String lastStateInReachability="";
               	    int i=heuristicResult.indexOf("_");
               	    if(i>=0){
               	    	lastStateInReachability=heuristicResult.substring(i+1);
               	    	heuristicResult=heuristicResult.substring(0,i);
               	    }
               	    
               	    boolean flag=false;
               	    if(heuristicResult==null)
               	    	heuristicResult="noreachability";
               	   
               	    if(heuristicResult.equals("reachability"))
               	    	flag=true;
               	    else
               	    	flag=false;
               	    
               	   if(rbdeadlock.isSelected()){
               		  if(heuristicResult.equals("reachability"))
                     	   	heuristicResult="The propery is verified."+"..Last state is: "+lastStateInReachability;
                     	else
                     	   	heuristicResult="The propery is not verified.";
               	   }
               	   if(rbreachability.isSelected()){
             		  if(heuristicResult.equals("reachability"))
                   	   	heuristicResult="The propery is verified."+"..Last state is: "+lastStateInReachability;
                   	 else
                   	   	heuristicResult="The propery is not verified.";
             	   }
	               	if(rbsafety.isSelected() ){
	           		  if(heuristicResult.equals("reachability"))
	                 	   	heuristicResult="The propery is refuted."+"..Last state is: "+lastStateInReachability;
	                 	 else
	                 	   	heuristicResult="The propery is not refuted.";
	           	   }
	               	if(rbLiveness.isSelected() ){
		           		  if(heuristicResult.equals("reachability"))
		                 	   	heuristicResult="The propery is refuted."+"..Last state is: "+lastStateInReachability;
		                 	 else
		                 	   	heuristicResult="The propery is not refuted.";
		           	 }
               	   
               	    
               	    
               	    txtresultOfmodelchecking.setText(heuristicResult);
               	    if(heuristicreach.isContinue && exploreGaBayesNet.goalStatesInfo.size()>0){
               	    	AllreportTime=exploreGaBayesNet.goalStatesInfo.get(0).foundTime-startTime;
               	    }else{
               	    	AllreportTime=System.currentTimeMillis() - startTime;
               	    }
               	    
               	   
               	                  	    
               	    
               	    String S1=String.valueOf(AllreportTime/1000.0);
               	    String S2=String.valueOf(heuristicreach.Number_Explored_States);
               	    String S3=String.valueOf(heuristicreach.First_Found_Dead_depth);
               	    String S4=String.valueOf(heuristicreach.Call_Number_Fitness);
               	    String S5=String.valueOf(heuristicreach.RunningTime_AllFitnessFuncs/1000.0);
               	 
               	    
               	    if(flag)
               	    	txtTimeSpent.setText(S1+" , " + S2 +" , " +S3+" , " +S4 +" , "+S5 );
               	    else
               	    	txtTimeSpent.setText("");
               	    
               	    
               	    if(heuristicreach.isContinue){
	               		 String s="";
	               		 for(i=1;i<=exploreGaBayesNet.goalStatesInfo.size()-1;i++){
	               			 ExploringGaBayesNet.GoalState goalstate=exploreGaBayesNet.goalStatesInfo.get(i);
	               			 AllreportTime=goalstate.foundTime-startTime;
	               			 if(i==1){
	               				 s="GoalState (2):"+" "+String.valueOf(AllreportTime/1000.0)+" -- "+String.valueOf(goalstate.witnessLength); 
	               			 }else{
	               				 s+="  GoalState ("+String.valueOf(i+1)+"): "+String.valueOf(AllreportTime/1000.0)+" -- "+String.valueOf(goalstate.witnessLength);
	               			 }
	               		 }
	               		 txtResultsOfAllGoals.setText(s);
	               	 }
               	    
               	    AllreportTime=0;
               	    
               		setCursor(new Cursor(Cursor.DEFAULT_CURSOR));
                }

                @Override
                public void refresh(Exploration exploration) {
                    setEnabled(START_TOOLTIP, exploration);
                }
            };
        }
        return this.startButton;
    }

    /** Initialises and returns the start button. */
    
    private RefreshButton getEnableHostGraphButton() {
        if (this.EnableHostGraphButton == null) {
            // Create the explore button (reference is needed when setting the
            // initial value of the (strategy/acceptor) editors.
            this.EnableHostGraphButton = new RefreshButton(Enable_HostGraph_COMMAND) {
                @Override
                public void execute() {
                	  
                	if(heuristicreach==null)
                		heuristicreach=new HeuBOA();
                	
               	 	
               	 	
                	long startTime = System.currentTimeMillis();
            	    
               	 	
               	 	
               	 	
                	
               	 	
               	    String HostGraphName;
               	    HostGraphName=cmbHostGraph.getSelectedItem().toString();
            	 	heuristicreach.simulator=simulator;
            	 	heuristicreach.HostGraphName=HostGraphName;
            	 	heuristicreach.EnableSelectedHostGraph();
               	 	
            	 
            	 	startButton.setEnabled(true);
            	 	
               	 	
                }

                @Override
                public void refresh(Exploration exploration) {
                    setEnabled(Enable_HostGraph_TOOLTIP, exploration);
                }
            };
        }
        return this.EnableHostGraphButton;
    }
   
    
    public long AllreportTime;
    public ExploringGaBayesNet exploreGaBayesNet;
    

    /** Initialises and returns the cancel button. */
    private RefreshButton getCancelButton() {
        if (this.cancelButton == null) {
            // Create the explore button (reference is needed when setting the
            // initial value of the (strategy/acceptor) editors.
            this.cancelButton = new RefreshButton(CANCEL_COMMAND) {
                @Override
                public void execute() {
                	//heuristicreach=null;
                    closeDialog();
                }

                @Override
                public void refresh(Exploration exploration) {
                    // do nothing
                }
            };
        }
        return this.cancelButton;
    }

    
    /**
     * Action that responds to Escape. Ensures that the dialog is closed.
     */
    private ActionListener createCloseListener() {
        return new ActionListener() {
            public void actionPerformed(ActionEvent actionEvent) {
                closeDialog();
                
            }
        };
    }
    /**
     * The close dialog action. Disposes dialog and resets DismissDelay of the
     * ToolTipManager.
     */
    private void closeDialog() {
        this.dispose();
    }
  
    private abstract class RefreshButton extends JButton {
        /** Constructs a refreshable button with a given button text. */
        public RefreshButton(String text) {
            super(text);
            addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    execute();
                }
            });
        }

        /** Callback action invoked on button click. */
        public abstract void execute();

        /** Callback action allowing the button to refresh its status. */
        public abstract void refresh(Exploration exploration);

        
        protected void setEnabled(String toolTipText, Exploration exploration) {
            setEnabled(true);
       }
    }
    
        
   
}
