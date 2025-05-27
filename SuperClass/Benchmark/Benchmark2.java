public class Benchmark2 {
    int a;
    int b;
    public Benchmark2(int x, int y) {
        a = x;
        b = y;
    }
    
    public int sum() {
        return a + b;
    }

    @Override
    public boolean equals(Object obj) {
    // Check if the object is compared with itself
    if (this == obj) {
        return true;
    }
    
    
    if (obj == null || getClass() != obj.getClass()) {
        return false;
    }
    
    
    Benchmark2 other = (Benchmark2) obj;
    
    // Compare the fields
    return this.a == other.a && this.b == other.b;
}

    
    public static void main(String[] args) {

        long startTime = System.currentTimeMillis();

        Benchmark2[] benchmarkArray = new Benchmark2[10000];
        
        for(int i=0;i<10000;++i)
        {
            benchmarkArray[i] = new Benchmark2(i*100,  i+1000);
        }
        
        for(int i=0;i<10000;++i)
        {
            for(int j=i+1;j<10000;++j)
            {
                if(benchmarkArray[i].equals(benchmarkArray[j]))
                {
                    // System.out.println("Objects are equal ");
                }
                else
                {
                    // System.out.println("Objects are not equal ");
                }
            }
        }
        
        
        
        long endTime = System.currentTimeMillis();
        
        System.out.println("Time taken: " + (endTime - startTime) + " ms");
    }

}
