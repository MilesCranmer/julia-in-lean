mktempdir() do root
    fake_home = joinpath(root, "home")
    sibling = joinpath(root, "home2")
    member = joinpath(sibling, "nested", "member")
    workspace_project = joinpath(root, "Project.toml")
    member_project = joinpath(member, "Project.toml")
    mkpath(fake_home)
    mkpath(member)
    write(workspace_project, "[workspace]\nprojects = [\"home2/nested/member\"]\n")
    write(member_project, "name = \"Member\"\n")
    old_home = get(ENV, "HOME", nothing)
    try
        ENV["HOME"] = fake_home
        found = Base.base_project(member_project)
        lexical_prefix = startswith(abspath(member_project), abspath(fake_home))
        inside_home = !startswith(relpath(member_project, fake_home), "..")
        println("homedir override          = ", homedir() == fake_home)
        println("project has home prefix   = ", lexical_prefix)
        println("project is inside home    = ", inside_home)
        println("workspace project exists  = ", isfile(workspace_project))
        println("base_project found        = ", found)
        if lexical_prefix && !inside_home && isfile(workspace_project) && found === nothing
            println("REPRODUCED loading-workspace-home-prefix")
        end
    finally
        old_home === nothing ? delete!(ENV, "HOME") : (ENV["HOME"] = old_home)
    end
end
