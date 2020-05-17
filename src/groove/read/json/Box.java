package groove.read.json;

import java.util.ArrayList;
import java.util.List;


public class Box {

	private ArrayList<Box> contents;
	private String id;

	public Box(String n) {
		this.id = n;
		this.contents = new ArrayList<Box>();
	}
	
	private String onString() {
		String ret="";
		for(Box b: this.contents)
			ret+= b.toString()+"\n";
		return ret;
	}

	public void addBox(Box b) {
		this.contents.add(b);
	}
	
	public List<Box> getBoxes(){
		return this.contents;
	}
	
	public String toString() {
		return this.id  + (this.onString().isEmpty()?" ":"\n"+this.onString());
	}
	

	
}
