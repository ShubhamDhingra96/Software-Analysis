package groove.read.json;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;

@SuppressWarnings("unused")
public class DemoRun {

	public static void main(String[] args) throws FileNotFoundException {

		// Make a bunch of boxes
		Box top = new Box("top");
		Box a = new Box("a");
		Box b = new Box("b");
		Box c = new Box("c");
		top.addBox(a);
		top.addBox(b);
		top.addBox(c);
		System.out.println(top);

		// declare a HashMap to store the mapping between box objects and Z3 strings
		HashMap<Box, String> mapping = new HashMap<>();

		// declare a List to store all the variable declarations
		ArrayList<String> variables = new ArrayList<>();

		// let's store here the feature model
		String featureModel = "";

		// parse the CSV mapping
		Scanner sc = new Scanner(new File("mapping.csv"));
		System.out.println(sc);
		sc.useDelimiter("\n");
		while (sc.hasNext()) {
			String line = sc.next();
			String[] parts = line.split(",");

			// if parts[0] is var then we have all the variable declarations
			if (parts[0].trim().equals("var")) {
				String allVariables = parts[1];
				String[] vars = allVariables.split(";"); // look in the CSV, I assume var decls are separated by ";"
				for (String v : vars)
					variables.add(v.trim());

			} else if (parts[0].trim().equals("featureModel")) { // we found the feature model constraint
				featureModel = parts[1].trim();
				System.out.println("frerrde" + featureModel);
				
			} else { // the line is in fact a feature mapping
				String boxName = parts[0];
				String presenceCondition = parts[1].trim();

				Box box = findBox(boxName, top);
				if (box != null)
					mapping.put(box, presenceCondition);
			}
		}
		sc.close();

		System.out.println("-------------------------");

		// Now the variables list has all variable declarations
		System.out.println(variables.toString());

		// Now the mapping HashMap contains pars of Box objects and Z3 strings
		System.out.println(mapping.toString());
		
		System.out.println("-------------------------");

		// So let's build the z3 string!
		
		String z3 = "\n";
		
		//Solver solver = loadSMTLIBEncoding(mapping, z3);

		// first the declare-fun for the boolean variables
		for (String v : variables)
			z3 += "(declare-fun " + v + " () Bool) \n";
	
		// then the feature model constraint
		z3 += "(assert "+featureModel+") \n";

		// and now the presence conditions
		for (Box x : mapping.keySet())
			z3+="(assert "+mapping.get(x).toString()+") \n";
		
		// and finally:
		z3 += "(check-sat) \n";

		System.out.println("jkrfnkjwrnfkjn" + z3);
		
		Solver solver = loadSMTLIBEncoding(mapping, featureModel);
		com.microsoft.z3.Status status = solver.check();
		System.out.println("ShuuUHNUKNUKN" + status);
		
		Model model = null;
		if ("SAT".equalsIgnoreCase(z3)) {
		//	model = Solver.getModel()
		} else if ("UNSAT".equalsIgnoreCase(z3)) {
		//	model = Solver.getModel()
			
		} else {
			System.out.println("Error");
		}
		
		
		
		//mapping.put("model","true");
			
	/*	try {
			
			com.microsoft.z3.Status status = solver.check();
			Model model = null;
			if (status == com.microsoft.z3.Status.SATISFIABLE) {
				model = solver.getModel();			
					
			} else {
				status = com.microsoft.z3.Status.UNSATISFIABLE;
				model = solver.getModel();
			}
				
		return null;

*/
	}


	private static Solver loadSMTLIBEncoding(HashMap<Box, String> config, String smtEncoding) {
		Context context = new Context();
		Solver solver = context.mkSolver();
		BoolExpr[] expr = context.parseSMTLIB2String(smtEncoding, null, null, null, null);
		solver.add(expr);

		return solver;
		}


	private static Box findBox(String name, Box topLevelBox) {
		List<Box> knownBoxes = topLevelBox.getBoxes();
		for (Box b : knownBoxes)
			if (b.toString().trim().equals(name))
				return b;
		return null;
	}

}
