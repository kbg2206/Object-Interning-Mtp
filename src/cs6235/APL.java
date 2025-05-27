
package cs6235;
import java.lang.reflect.Field;

public class APL {
	Object node;
	APL next;
	
	APL(Object node_){
		node = node_;
		next = null;
	}

	public static Object search(APL apl, Object thatObj, String className) {

		APL curr = apl;
		while(curr != null) {
			
			Object thisObj = curr.node;
			try {
	            
	            Class<?> clazz = Class.forName(className);
	           
	            if (clazz.isInstance(thisObj)) {

	            	Field[] thisObjFields = thisObj.getClass().getDeclaredFields();
	                Field[] thatObjFields = thatObj.getClass().getDeclaredFields();
	                
	                if(thisObjFields.length != thatObjFields.length)
	                	return false;
	                
	                int flag=1;
	                for(int i=0;i<thatObjFields.length; i++) {
	                	System.out.println(thatObjFields[i] + " value:-"+ thatObjFields[i].get(thatObj));
	                	System.out.println(thisObjFields[i] + " value1:-"+ thisObjFields[i].get(thisObj));
	                	if(!thatObjFields[i].get(thatObj).equals(thisObjFields[i].get(thisObj))) {
	                		flag=0;
	                		break;
	                	}
	                }
	                if(flag == 1) {
	                	System.out.println("Object found " );
	                	return thisObj;
	                }
	            } else {
	                System.out.println("Cannot cast to " + className);
	            }
	        } catch (ClassNotFoundException e) {
	            System.out.println("Class not found: " + className);
	        } catch (IllegalArgumentException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			curr = curr.next;
	    }
		return null;
	}
	
	public static void insert(APL firstNode, APL newNode) {
		
		newNode.next = firstNode;
		
	}

}

//No need to cast
//Object castedObject = clazz.cast(thisObj);
//Field[] thisObjFields = castedObject.getClass().getDeclaredFields();

